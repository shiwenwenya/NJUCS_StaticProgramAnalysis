/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(Invoke invokeStmt) {// x = T.m();
            if (invokeStmt.isStatic()) {
                addReachable(invokeStmt.getMethodRef().resolve());
                for (int i = 0; i < invokeStmt.getInvokeExp().getArgCount(); i++) {
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(invokeStmt.getInvokeExp().getArg(i)),
                            pointerFlowGraph.getVarPtr(invokeStmt.getMethodRef().resolve().getIR().getParam(i))
                    );
                }
                if (invokeStmt.getLValue() != null) {
                    for (Var returnVar : invokeStmt.getMethodRef().resolve().getIR().getReturnVars()) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(returnVar),
                                pointerFlowGraph.getVarPtr(invokeStmt.getLValue())
                        );
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(New newStmt) {// x = new T();
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(newStmt.getLValue()),
                    new PointsToSet(heapModel.getObj(newStmt))
            );
            return null;
        }

        @Override
        public Void visit(Copy copyStmt) {// x = y;
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(copyStmt.getRValue()),
                    pointerFlowGraph.getVarPtr(copyStmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(StoreField storeFieldStmt) {// T.f = y;
            if (storeFieldStmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(storeFieldStmt.getRValue()),
                        pointerFlowGraph.getStaticField(storeFieldStmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(LoadField loadFieldStmt) {// y = T.f;
            if (loadFieldStmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getStaticField(loadFieldStmt.getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(loadFieldStmt.getLValue())
                );
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {// if s → t ∉ PFG then add s → t to PFG
            if (!source.getPointsToSet().isEmpty()) {// if pt(s) is not empty then
                workList.addEntry(target, source.getPointsToSet());// add <t, pt(s)> to WL
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {// while WL is not empty do
            WorkList.Entry entry = workList.pollEntry();// remove from WL
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());// Propagate(n, Δ)
            if (entry.pointer() instanceof VarPtr varPtr) {// if n represents a variable x then
                Var var = varPtr.getVar();
                for (Obj obj : delta) {// foreach 𝑜𝑖 ∈ Δ do
                    for (StoreField storeField : var.getStoreFields()) {// x.f = y;
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve())
                        );// AddEdge(y, 𝑜𝑖.𝑓)
                    }
                    for (LoadField loadField : var.getLoadFields()) {// y = x.f;
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(loadField.getLValue())
                        );// AddEdge(𝑜𝑖.𝑓, y)
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {// x[i] = y;
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {// y = x[i];
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(loadArray.getLValue())
                        );
                    }
                    processCall(var, obj);// ProcessCall(x, 𝑜𝑖)
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        for (Obj obj : pointsToSet) {// Δ = pts – pt(n)
            if (!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {// if pts is not empty then
            for (Obj obj : delta) {// pt(n) ⋃= pts
                pointer.getPointsToSet().addObject(obj);
            }
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {// add s, pts to WL
                workList.addEntry(succ, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke : var.getInvokes()) {
            if (invoke.isStatic()) continue;
            JMethod method = resolveCallee(recv, invoke);// 𝑚 = Dispatch(𝑜𝑖, k)
            workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()), new PointsToSet(recv));// add to WL
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))) {// if l → 𝑚 ∉ CG then add l → 𝑚 to CG
                addReachable(method);// AddReachable(𝑚)
                for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {// AddEdge(𝑎𝑖, 𝑝𝑖)
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)),
                            pointerFlowGraph.getVarPtr(method.getIR().getParam(i))
                    );
                }
                if (invoke.getLValue() != null) {
                    for (Var returnVar : method.getIR().getReturnVars()) {// AddEdge(𝑚𝑟, 𝑟)
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(returnVar),
                                pointerFlowGraph.getVarPtr(invoke.getLValue())
                        );
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
