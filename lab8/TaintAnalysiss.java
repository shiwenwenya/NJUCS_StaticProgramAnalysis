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

package pascal.taie.analysis.pta.plugin.taint;

import pascal.taie.util.collection.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public Obj processSource(Invoke invoke, JMethod callee) {
        if (config.getSources().contains((new Source(callee, callee.getReturnType())))) {
            return manager.makeTaint(invoke, callee.getReturnType());
        }
        return null;
    }

    public Set<Pair<Var, Obj>> processTransfer(CSCallSite csCallSite, JMethod callee, CSVar recv) {
        solver.getResult();
        Set<Pair<Var, Obj>> result = new HashSet<>();
        TaintTransfer taintTransfer;
        if (recv != null) {
            // Call (base-to-result)
            taintTransfer = new TaintTransfer(callee, TaintTransfer.BASE, TaintTransfer.RESULT, callee.getReturnType());
            if (csCallSite.getCallSite().getLValue() != null && config.getTransfers().contains(taintTransfer)) {
                for (CSObj csObj : solver.getResult().getPointsToSet(recv)) {
                    if (manager.isTaint(csObj.getObject())) {
                        result.add(new Pair<>(
                                csCallSite.getCallSite().getLValue(),
                                manager.makeTaint(manager.getSourceCall(csObj.getObject()), callee.getReturnType())
                        ));
                    }
                }
            }
            // Call (arg-to-base)
            for (int i = 0; i < csCallSite.getCallSite().getInvokeExp().getArgs().size(); i++) {
                taintTransfer = new TaintTransfer(callee, i, TaintTransfer.BASE, recv.getType());
                if (config.getTransfers().contains(taintTransfer)) {
                    for (CSObj csObj : solver.getResult().getPointsToSet(csManager.getCSVar(
                            csCallSite.getContext(),
                            csCallSite.getCallSite().getInvokeExp().getArgs().get(i)
                    ))) {
                        if (manager.isTaint(csObj.getObject())) {
                            result.add(new Pair<>(recv.getVar(), manager.makeTaint(manager.getSourceCall(csObj.getObject()), recv.getType())));
                        }
                    }
                }
            }
        }
        // Call (arg-to-result)
        for (int i = 0; i < csCallSite.getCallSite().getInvokeExp().getArgs().size(); i++) {
            taintTransfer = new TaintTransfer(callee, i, TaintTransfer.RESULT, callee.getReturnType());
            if (config.getTransfers().contains(taintTransfer)) {
                for (CSObj csObj : solver.getResult().getPointsToSet(csManager.getCSVar(
                        csCallSite.getContext(),
                        csCallSite.getCallSite().getInvokeExp().getArgs().get(i)
                ))) {
                    if (manager.isTaint(csObj.getObject())) {
                        result.add(new Pair<>(
                                csCallSite.getCallSite().getLValue(),
                                manager.makeTaint(manager.getSourceCall(csObj.getObject()), callee.getReturnType())
                        ));
                    }
                }
            }
        }
        return result;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        for (CSMethod csMethod : result.getCSCallGraph().reachableMethods().toList()) {
            for (CSCallSite csCallSite : result.getCSCallGraph().getCallersOf(csMethod)) {
                for (int i = 0; i < csCallSite.getCallSite().getInvokeExp().getArgs().size(); i++) {
                    if (config.getSinks().contains(new Sink(csMethod.getMethod(), i))) {
                        for (Obj obj : result.getPointsToSet(csCallSite.getCallSite().getInvokeExp().getArgs().get(i))) {
                            if (manager.isTaint(obj)) {
                                taintFlows.add(new TaintFlow(manager.getSourceCall(obj), csCallSite.getCallSite(), i));
                            }
                        }
                    }
                }
            }
        }
        return taintFlows;
    }
}