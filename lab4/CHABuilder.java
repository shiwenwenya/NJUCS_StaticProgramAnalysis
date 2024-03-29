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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod jMethod = workList.poll();
            if (!callGraph.contains(jMethod)) {
                callGraph.addReachableMethod(jMethod);
                for (Invoke callSite : callGraph.getCallSitesIn(jMethod)) {
                    for (JMethod newMethod : resolve(callSite)) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, newMethod));
                        workList.add(newMethod);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> ans = new HashSet<>();
        if (callSite.isStatic()) {
            ans.add(callSite.getMethodRef().getDeclaringClass().getDeclaredMethod(callSite.getMethodRef().getSubsignature()));
        } else if (callSite.isSpecial()) {
            JMethod jMethod = dispatch(callSite.getMethodRef().getDeclaringClass(), callSite.getMethodRef().getSubsignature());
            if (jMethod != null) {
                ans.add(jMethod);
            }
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            Queue<JClass> JClassqueue = new LinkedList<>();
            JClass rootJClass = callSite.getMethodRef().getDeclaringClass();
            JClassqueue.add(rootJClass);
            while (!JClassqueue.isEmpty()) {
                JClass jClass = JClassqueue.poll();
                JMethod jMethod = dispatch(jClass, callSite.getMethodRef().getSubsignature());
                if (jMethod != null) {
                    ans.add(jMethod);
                }
                if (jClass.isInterface()) {
                    JClassqueue.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                    JClassqueue.addAll(hierarchy.getDirectImplementorsOf(jClass));
                } else {
                    JClassqueue.addAll(hierarchy.getDirectSubclassesOf(jClass));
                }
            }
        }
        return ans;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass != null) {
            JMethod jMethod = jclass.getDeclaredMethod(subsignature);
            if (jMethod != null && !jMethod.isAbstract()) {
                return jMethod;
            } else {
                return dispatch(jclass.getSuperClass(), subsignature);
            }
        }
        return null;
    }
}
