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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (!callGraph.contains(csMethod)) {//if c:m ∉ RM then
            callGraph.addReachableMethod(csMethod);//add c:m to RM
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(new StmtProcessor(csMethod));
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(Invoke invokeStmt) {// x = T.m();
            if (!invokeStmt.isStatic()) {
                return null;
            }
            JMethod callee = resolveCallee(null, invokeStmt);
            CSCallSite csCallSite = csManager.getCSCallSite(context, invokeStmt);
            Context calleeContext = contextSelector.selectContext(csCallSite, callee);
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csManager.getCSMethod(calleeContext, callee)))) {
                addReachable(csManager.getCSMethod(calleeContext, callee));
                for (int i = 0; i < invokeStmt.getInvokeExp().getArgCount(); i++) {
                    addPFGEdge(
                            csManager.getCSVar(context, invokeStmt.getInvokeExp().getArg(i)),
                            csManager.getCSVar(calleeContext, callee.getIR().getParam(i))
                    );
                }
                if (invokeStmt.getLValue() != null) {
                    for (Var returnVar : callee.getIR().getReturnVars()) {
                        addPFGEdge(
                                csManager.getCSVar(calleeContext, returnVar),
                                csManager.getCSVar(context, invokeStmt.getLValue())
                        );
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(New newStmt) {// x = new T();
            workList.addEntry(
                    csManager.getCSVar(context, newStmt.getLValue()),
                    PointsToSetFactory.make(csManager.getCSObj(
                            contextSelector.selectHeapContext(csMethod, heapModel.getObj(newStmt)),
                            heapModel.getObj(newStmt))
                    )
            );
            return null;
        }

        @Override
        public Void visit(Copy copyStmt) {// x = y;
            addPFGEdge(
                    csManager.getCSVar(context, copyStmt.getRValue()),
                    csManager.getCSVar(context, copyStmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(StoreField storeFieldStmt) {// T.f = y;
            if (storeFieldStmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(context, storeFieldStmt.getRValue()),
                        csManager.getStaticField(storeFieldStmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(LoadField loadFieldStmt) {// y = T.f;
            if (loadFieldStmt.isStatic()) {
                addPFGEdge(
                        csManager.getStaticField(loadFieldStmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, loadFieldStmt.getLValue())
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
            if (entry.pointer() instanceof CSVar csVar) {// if n represents a variable c:x then
                Var var = csVar.getVar();
                for (CSObj obj : delta) {// foreach  c′:𝑜𝑖 ∈ Δ do
                    for (StoreField storeField : var.getStoreFields()) {// x.f = y;
                        addPFGEdge(
                                csManager.getCSVar(csVar.getContext(), storeField.getRValue()),
                                csManager.getInstanceField(obj, storeField.getFieldRef().resolve())
                        );// AddEdge(c:y, c′:𝑜𝑖.f)

                    }
                    for (LoadField loadField : var.getLoadFields()) {// y = x.f;
                        addPFGEdge(
                                csManager.getInstanceField(obj, loadField.getFieldRef().resolve()),
                                csManager.getCSVar(csVar.getContext(), loadField.getLValue())
                        );// AddEdge(c′:𝑜𝑖.f, c:y)
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {// x[i] = y;
                        addPFGEdge(
                                csManager.getCSVar(csVar.getContext(), storeArray.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {// y = x[i];
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(csVar.getContext(), loadArray.getLValue())
                        );
                    }
                    processCall(csVar, obj);// ProcessCall(c:x, c′:𝑜𝑖)
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
        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj csObj : pointsToSet.getObjects()) {// Δ = pts – pt(n)
            if (!pointer.getPointsToSet().contains(csObj)) {
                delta.addObject(csObj);
            }
        }
        if (!delta.isEmpty()) {// if pts is not empty then
            for (CSObj csObj : delta) {// pt(n) ⋃= pts
                pointer.getPointsToSet().addObject(csObj);
            }
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {// foreach n → s ∈ PFG do
                workList.addEntry(succ, delta);// add s, pts to WL
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (Invoke invoke : recv.getVar().getInvokes()) {// foreach l: r = x.k(a1,…,an) ∈ S do
            if (invoke.isStatic()) continue;
            JMethod callee = resolveCallee(recvObj, invoke);// m = Dispatch(𝑜𝑖, k)
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);// 𝑐𝑡 = Select(c, l, 𝑐′:𝑜𝑖)
            workList.addEntry(csManager.getCSVar(calleeContext, callee.getIR().getThis()), PointsToSetFactory.make(recvObj));// add to WL
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csManager.getCSMethod(calleeContext, callee)))) {// if c:l → 𝑐𝑡:m ∉ CG then
                addReachable(csManager.getCSMethod(calleeContext, callee));// AddReachable(𝑐𝑡:𝑚)
                for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
                    addPFGEdge(
                            csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArg(i)),
                            csManager.getCSVar(calleeContext, callee.getIR().getParam(i))
                    );
                }// AddEdge(c:𝑎𝑖, 𝑐𝑡:𝑝𝑖)
                if (invoke.getLValue() != null) {
                    for (Var returnVar : callee.getIR().getReturnVars()) {
                        addPFGEdge(
                                csManager.getCSVar(calleeContext, returnVar),
                                csManager.getCSVar(recv.getContext(), invoke.getLValue())
                        );
                    }// AddEdge(𝑐𝑡: 𝑚𝑟, c:r)
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
