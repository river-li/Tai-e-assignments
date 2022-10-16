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
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.*;
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
        ArrayDeque<JMethod> workload = new ArrayDeque<>();
        workload.add(entry);
        while(!workload.isEmpty()){
            JMethod m = workload.poll();
            callGraph.addReachableMethod(m);
            callGraph.callSitesIn(m).forEach(cs->{
                Set<JMethod> methods = resolve(cs);
                for(JMethod m1:methods){
                    callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(cs), cs, m1));
                    if(callGraph.reachableMethods.contains(m1)){
                        continue;
                    }
                    // 这里之前的顺序不太对，continue这一句应该放在addEdge后面，因为不管这个函数是否reachable都应该把边加进去
                    workload.add(m1);
                }
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod>result = new LinkedHashSet<JMethod>();

        CallKind calltype = CallGraphs.getCallKind(callSite);
        if (calltype == CallKind.STATIC){
            result.add(callSite.getMethodRef().getDeclaringClass().getDeclaredMethod(
                    callSite.getMethodRef().getSubsignature()
            ));
        }
        else if (calltype == CallKind.SPECIAL){
            result.add(dispatch(callSite.getMethodRef().getDeclaringClass(),callSite.getMethodRef().getSubsignature()));
        }
        else if (calltype == CallKind.VIRTUAL || calltype == CallKind.INTERFACE) {
            JClass c = callSite.getMethodRef().getDeclaringClass();
            Subsignature sig = callSite.getMethodRef().getSubsignature();
            Queue<JClass> q = new ArrayDeque<JClass>();
            q.add(c);
            while (!q.isEmpty()){
                JClass tempc = q.poll();
                JMethod m = dispatch(tempc, sig);
                if (m!=null){
                    result.add(m);
                }
                q.addAll(hierarchy.getDirectSubclassesOf(tempc));
                q.addAll(hierarchy.getDirectImplementorsOf(tempc));
                q.addAll(hierarchy.getDirectSubinterfacesOf(tempc));
            }
        }

        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null){
            return null;
        }
        JMethod m = jclass.getDeclaredMethod(subsignature);
        if (m!=null){
            // 如果jclass存在非抽象方法m'
            if (!m.isAbstract()){
                return m;
            }
        }
        return dispatch(jclass.getSuperClass(), subsignature);
//        return null;
    }
}
