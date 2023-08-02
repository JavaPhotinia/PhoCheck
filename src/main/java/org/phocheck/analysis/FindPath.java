package org.phocheck.analysis;

import soot.Hierarchy;
import soot.MethodOrMethodContext;
import soot.SootMethod;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Targets;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Stack;

public class FindPath {
    public Stack<SootMethod> stack = new Stack<>();
    public HashSet<Stack<SootMethod>> paths = new HashSet<>();
    public CallGraph cg;
    private final int CIRCLE_COUNT = 30;

    public FindPath(CallGraph cg, Hierarchy hierarchy) {
        this.cg = cg;
    }

    public HashSet<Stack<SootMethod>> getPaths() {
        HashSet<Stack<SootMethod>> paths = (HashSet<Stack<SootMethod>>) this.paths.clone();
        this.paths.clear();
        return paths;
    }

    public boolean isSootMethodInStack(SootMethod node) {
        for (SootMethod next : stack) {
            if (node == next)
                return true;
        }
        return false;
    }

    public void saveEntryPoints() {
        if (stack.size() > 2) {
            Stack<SootMethod> clone = (Stack<SootMethod>) stack.clone();
            paths.add(clone);
        }
    }

    public boolean computedPath(SootMethod cSootMethod, SootMethod pSootMethod, SootMethod sSootMethod) {
        SootMethod nSootMethod;
        if (pSootMethod != null && cSootMethod == pSootMethod)
            return false;
        if (stack.size() >= CIRCLE_COUNT) {
            return false;
        }

        if (cSootMethod != null) {
            Iterator<MethodOrMethodContext> targets = new Targets(cg.edgesOutOf(cSootMethod));
            ArrayList<SootMethod> relationSootMethods = new ArrayList<>();
            while (targets.hasNext()) {
                SootMethod relationSootMethod = (SootMethod) targets.next();
                if (skipMethod(relationSootMethod)) {
                    continue;
                }
                if (!relationSootMethods.contains(relationSootMethod))
                    relationSootMethods.add(relationSootMethod);
            }
            int i = 0;
            stack.push(cSootMethod);
            if (relationSootMethods.size() == 0) {
                if (cSootMethod == sSootMethod) {
                    saveEntryPoints();
                    stack.pop();
                    return true;
                }
                saveEntryPoints();
                return true;
            }
            else {
                nSootMethod = relationSootMethods.get(i);
                while (nSootMethod != null) {
                    if (pSootMethod != null && (nSootMethod == sSootMethod || nSootMethod == pSootMethod || isSootMethodInStack(nSootMethod))) {
                        saveEntryPoints();
                        i++;
                        if (i >= relationSootMethods.size())
                            nSootMethod = null;
                        else
                            nSootMethod = relationSootMethods.get(i);
                        continue;
                    }
                    if (computedPath(nSootMethod, cSootMethod, sSootMethod)) {
                        stack.pop();
                    }
                    i++;
                    if (i >= relationSootMethods.size())
                        nSootMethod = null;
                    else
                        nSootMethod = relationSootMethods.get(i);
                }
                stack.pop();
                return false;
            }
        } else
            return false;
    }

    private boolean skipMethod(SootMethod sootMethod) {
        if (sootMethod.getName().contains("clinit") || sootMethod.isJavaLibraryMethod()
                || sootMethod.getName().contains("callConfig_synthetic") || sootMethod.getDeclaringClass().getName().contains("org.apache")
                || sootMethod.getDeclaringClass().getName().contains("synthetic.method.datatable")
                || sootMethod.getDeclaringClass().getName().contains("synthetic.method.SingletonFactory")
                || ((sootMethod.getDeclaringClass().getName().contains("$$SpringCGLIB") || sootMethod.getDeclaringClass().getName().contains("$$InterceptorProxy")) && sootMethod.getName().contains("get") && sootMethod.getName().contains("Instance"))
                || ((sootMethod.getDeclaringClass().getName().contains("$$SpringCGLIB") || sootMethod.getDeclaringClass().getName().contains("$$InterceptorProxy")) && sootMethod.getName().contains("getString"))
                || sootMethod.getDeclaringClass().getName().contains("com.alibaba.fastjson.JSON")
                || (sootMethod.getDeclaringClass().getName().contains("org.springframework") && !sootMethod.getDeclaringClass().getName().contains("org.springframework.security"))) {
            return true;
        }
        return false;
    }
}
