package org.phocheck.analysis;

import org.phocheck.bean.SourceAndSinkBean;
import soot.Hierarchy;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.jimple.toolkits.callgraph.CallGraph;

import java.util.*;

import static analysis.CreateEdge.projectMainMethod;


public class AccessControlTransformer extends SceneTransformer {
    private final HashSet<String> authMethods = new HashSet<>();
    private final HashSet<String> loginMethods = new HashSet<>();
    private final Map<String, SourceAndSinkBean> vulPathMap = new HashMap<>();
    private final RetValueDataFlowAnalysis retValueDataFlowAnalysis = new RetValueDataFlowAnalysis();

    public AccessControlTransformer() {
        super();
    }

    @Override
    protected void internalTransform(String s, Map<String, String> map) {
        CallGraph cg = Scene.v().getCallGraph();
        Hierarchy hierarchy = Scene.v().getActiveHierarchy();
        FindPath findPath = new FindPath(cg, hierarchy);
        DataFlowAnalysis dataFlowAnalysis = new DataFlowAnalysis(cg);

        System.out.println("Start compute path!");
        findPath.computedPath(projectMainMethod, null, projectMainMethod);
        HashSet<Stack<SootMethod>> paths = findPath.getPaths();
        findAuthMethod(paths);
        HashSet<Stack<SootMethod>> resourcePaths = collectPathWithResource(paths);
        paths.removeAll(resourcePaths);
        System.out.println("start auth check phase 1!");
        HashSet<Stack<SootMethod>> vulPaths = collectPathWithoutAuth(resourcePaths);
        System.out.println("Find path without auth: " + vulPaths.size());
        System.out.println("start auth check phase 2!");
        HashSet<Stack<SootMethod>> pathWithAuth = filterPathWithAuth(resourcePaths);
        System.out.println("Phase 1: Find path with auth: " + pathWithAuth.size());
        HashSet<SootMethod> resourcePoints = collectResourceMethod(pathWithAuth);
        HashSet<Stack<SootMethod>> pathWithoutAuth = filterPathWithoutAuth(resourcePaths, pathWithAuth);
        HashSet<Stack<SootMethod>> vulPaths2 = accessControllerOne(pathWithoutAuth, resourcePoints);
        System.out.println("Phase 2: Find path without auth: " + vulPaths2.size());

        System.out.println("start auth check phase 3!");
        HashSet<Stack<SootMethod>> vulPaths3 = accessControllerTwo(resourcePaths);
        System.out.println("Phase 3: Find path without auth: " + vulPaths3.size());
        System.out.println("Total find path without auth: " + (vulPaths.size() + vulPaths2.size() + vulPaths3.size()));
        for (String key : vulPathMap.keySet()) {
            SourceAndSinkBean ssb = vulPathMap.get(key);
            System.out.println(ssb.getSinkMethod().getSignature() + " -> _SINK_");
            int num = 1;
            // for (String path : ssb.getPath()) {
            //     System.out.println("vul path " + num + ": " + path);
            //     num++;
            // }
        }
    }

    private HashSet<Stack<SootMethod>> collectPathWithResource(HashSet<Stack<SootMethod>> paths) {
        HashSet<Stack<SootMethod>> resourcePaths = new HashSet<>();
        for (Stack<SootMethod> path : paths) {
            for (int i = 0; i < path.size(); i++) {
                SootMethod popMethod = path.elementAt(i);
                if (isResourcePoint(popMethod)
                        && (popMethod.getDeclaringClass().getName().contains("RepositoryImpl")
                        || popMethod.getDeclaringClass().getName().contains("MapperImpl")
                        || popMethod.getDeclaringClass().getName().contains("DaoImpl"))) {
                    int lenth = path.size();
                    for (int j = 0; j < lenth - i - 1; j++) {
                        path.pop();
                    }
                    resourcePaths.add(path);
                    break;
                }
            }
        }
        return resourcePaths;
    }

    private HashSet<Stack<SootMethod>> collectPathWithoutAuth(HashSet<Stack<SootMethod>> paths) {
        HashSet<Stack<SootMethod>> vulPaths = new HashSet<>();
        for (Stack<SootMethod> path : paths) {
            ArrayList<SootMethod> vulpath = new ArrayList<>();
            for (int i = 0; i < path.size(); i++) {
                SootMethod popMethod = path.elementAt(i);
                vulpath.add(popMethod);
                if (popMethod.getName().contains("doFilter")
                        || (popMethod.getSignature().contains("org.springframework.security.") && popMethod.getSignature().contains("Filter"))
                        || authMethods.contains(path.elementAt(i).getSignature())) {
                    break;
                } else if (isResourcePoint(popMethod)
                        && (popMethod.getDeclaringClass().getName().contains("RepositoryImpl")
                        || popMethod.getDeclaringClass().getName().contains("MapperImpl")
                        || popMethod.getDeclaringClass().getName().contains("DaoImpl"))) {
                    boolean keyResourceOperate = false;
                    if (popMethod.getName().contains("delete")
                            || popMethod.getName().contains("update")
                            || popMethod.getName().contains("add")
                            || popMethod.getName().contains("save")
                            || popMethod.getName().contains("insert")) {
                        keyResourceOperate = true;
                    } else if (popMethod.getName().contains("select") || popMethod.getName().contains("find") || popMethod.getName().contains("count")) {
                        if (retValueDataFlowAnalysis.checkReturnValue((Stack<SootMethod>) path.clone())) {
                            keyResourceOperate = true;
                        }
                    }
                    if (keyResourceOperate) {
                        vulPaths.add(path);
                        if (vulPathMap.containsKey(popMethod.getSignature())) {
                            vulPathMap.get(popMethod.getSignature()).addPath(vulpath.toString());
                        } else {
                            SourceAndSinkBean ssb = new SourceAndSinkBean();
                            ssb.setSourceMethod(vulpath.get(0));
                            ssb.setSinkMethod(popMethod);
                            ssb.addPath(vulpath.toString());
                            vulPathMap.put(popMethod.getSignature(), ssb);
                        }
                        break;
                    }
                }
            }
        }
        paths.removeAll(vulPaths);
        return vulPaths;
    }


    private HashSet<Stack<SootMethod>> accessControllerOne(HashSet<Stack<SootMethod>> paths, HashSet<SootMethod> resources) {
        HashSet<Stack<SootMethod>> vulPaths = new HashSet<>();
        for (Stack<SootMethod> path : paths) {
            int countMatch = 0;
            boolean isService = false;
            ArrayList<SootMethod> vulpath = new ArrayList<>();
            for (int i = 0; i < path.size(); i++) {
                vulpath.add(path.elementAt(i));
                if (resources.contains(path.elementAt(i))) {
                    countMatch++;
                }
                if (path.elementAt(i).getName().contains("callEntry_")) {
                    isService = true;
                }
                if (countMatch >= 2 && isService && isResourcePoint(path.elementAt(i))
                        && (path.elementAt(i).getDeclaringClass().getName().contains("RepositoryImpl")
                        || path.elementAt(i).getDeclaringClass().getName().contains("MapperImpl")
                        || path.elementAt(i).getDeclaringClass().getName().contains("DaoImpl"))) {
                    vulPaths.add(path);
                    if (vulPathMap.containsKey(path.elementAt(i).getSignature())) {
                        vulPathMap.get(path.elementAt(i).getSignature()).addPath(path.toString());
                    } else {
                        SourceAndSinkBean ssb = new SourceAndSinkBean();
                        ssb.setSourceMethod(path.firstElement());
                        ssb.setSinkMethod(path.elementAt(i));
                        ssb.addPath(vulpath.toString());
                        vulPathMap.put(path.elementAt(i).getSignature(), ssb);
                    }
                    break;
                }
            }
        }
        return vulPaths;
    }

    private HashSet<Stack<SootMethod>> accessControllerTwo(HashSet<Stack<SootMethod>> paths) {
        HashSet<Stack<SootMethod>> vulPaths = new HashSet<>();
        for (Stack<SootMethod> path : paths) {
            ArrayList<SootMethod> vulpath = new ArrayList<>();
            int authNum = 0;
            for (int i = 0; i < path.size(); i++) {
                vulpath.add(path.elementAt(i));
                if (authMethods.contains(path.elementAt(i).getSignature())) {
                    authNum++;
                }
                if (loginMethods.contains(path.elementAt(i).getSignature())) {
                    authNum--;
                }
                if (path.elementAt(i).getName().contains("preHandle")) {
                    authNum++;
                }
                if (isResourcePoint(path.elementAt(i))
                        && (path.elementAt(i).getDeclaringClass().getName().contains("RepositoryImpl")
                        || path.elementAt(i).getDeclaringClass().getName().contains("MapperImpl")
                        || path.elementAt(i).getDeclaringClass().getName().contains("DaoImpl"))) {
                    break;
                }
            }
            if (authNum < 1) {
                vulPaths.add(path);
                if (vulPathMap.containsKey(vulpath.get(vulpath.size() - 1).getSignature())) {
                    vulPathMap.get(vulpath.get(vulpath.size() - 1).getSignature()).addPath(path.toString());
                } else {
                    SourceAndSinkBean ssb = new SourceAndSinkBean();
                    ssb.setSourceMethod(path.firstElement());
                    ssb.setSinkMethod(vulpath.get(vulpath.size() - 1));
                    ssb.addPath(vulpath.toString());
                    vulPathMap.put(vulpath.get(vulpath.size() - 1).getSignature(), ssb);
                }
            }
        }
        return vulPaths;
    }

    private void findAuthMethod(HashSet<Stack<SootMethod>> paths) {
        for (Stack<SootMethod> path : paths) {
            HashSet<String> loginMethodSet = new HashSet<>();
            for (int i = 0; i < path.size(); i++) {
                SootMethod sootMethod = path.elementAt(i);
                if (sootMethod.getName().contains("preHandle")) {
                    authMethods.add(path.elementAt(i - 1).getSignature());
                    loginMethodSet.add(path.elementAt(i - 1).getSignature());
                    continue;
                } else if (sootMethod.getParameterTypes().toString().contains("org.aspectj.lang.ProceedingJoinPoint")) {
                    if (skipAuthMethod(sootMethod)) continue;
                    authMethods.add(path.elementAt(i).getSignature());
                    loginMethodSet.add(path.elementAt(i).getSignature());
                    continue;
                } else if (sootMethod.getSignature().contains("org.springframework.security.") && path.elementAt(i).getSignature().contains("Filter")) {
                    authMethods.add(path.elementAt(i).getSignature());
                    continue;
                } else if (sootMethod.getName().contains("doFilter")) {
                    authMethods.add(path.elementAt(i).getSignature());
                    continue;
                }
                if (loginMethodSet.size() != 0
                        && (sootMethod.getName().toLowerCase().contains("sign") ||
                        sootMethod.getName().toLowerCase().contains("login"))) {
                    loginMethods.addAll(loginMethodSet);
                }
            }
        }
    }

    private boolean skipAuthMethod(SootMethod sootMethod) {
        if (sootMethod.getSignature().contains("org.jeecg.common.aspect.DictAspect: java.lang.Object doAround")) {
            return true;
        }
        return false;
    }

    private HashSet<Stack<SootMethod>> filterPathWithAuth(HashSet<Stack<SootMethod>> paths) {
        HashSet<Stack<SootMethod>> filterPaths = new HashSet<>();
        for (Stack<SootMethod> path : paths) {
            for (int i = 0; i < path.size(); i++) {
                SootMethod popMethod = path.elementAt(i);
                if (popMethod.getName().contains("doFilter")
                        || (popMethod.getSignature().contains("org.springframework.security.") && popMethod.getSignature().contains("Filter"))
                        || authMethods.contains(popMethod.getSignature())) {
                    filterPaths.add(path);
                }
            }
        }
        return filterPaths;
    }

    private HashSet<Stack<SootMethod>> filterPathWithoutAuth(HashSet<Stack<SootMethod>> paths, HashSet<Stack<SootMethod>> removePaths) {
        HashSet<Stack<SootMethod>> filterPaths = (HashSet<Stack<SootMethod>>) paths.clone();
        filterPaths.removeAll(removePaths);
        paths.removeAll(filterPaths);
        return filterPaths;
    }


    private HashSet<SootMethod> collectResourceMethod(HashSet<Stack<SootMethod>> paths) {
        HashSet<SootMethod> resourceMethod = new HashSet<>();
        for (Stack<SootMethod> path : paths) {
            Stack<SootMethod> clonePath = (Stack<SootMethod>) path.clone();
            while (!clonePath.isEmpty() && !clonePath.peek().getName().contains("doFilter")
                    && !clonePath.peek().getName().contains("$$InterceptorProxy")
                    && !clonePath.peek().getName().contains("$$SpringCGLIB")) {
                SootMethod popMethod = clonePath.pop();
                if (isResourcePoint(popMethod)) {
                    resourceMethod.add(popMethod);
                }
            }
        }
        return resourceMethod;
    }

    private boolean isResourcePoint(SootMethod sootMethod) {
        if (sootMethod.isPhantom() || sootMethod.getDeclaringClass().getName().contains("org.slf4j.")
                || sootMethod.getDeclaringClass().getName().contains("org.apache.")
                || sootMethod.getDeclaringClass().getName().contains("synthetic.method.PostRepositoryImpl")
                || sootMethod.getDeclaringClass().getName().contains("org.springframework.")) {
            return false;
        }
        return true;
    }
}
