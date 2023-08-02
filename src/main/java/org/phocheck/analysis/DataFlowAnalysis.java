package org.phocheck.analysis;


import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.Sources;
import soot.tagkit.AnnotationTag;
import soot.tagkit.Tag;
import soot.tagkit.VisibilityAnnotationTag;
import soot.util.Chain;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class DataFlowAnalysis {
    private String variable;
    private HashSet<Integer> indexSet = new HashSet<>();
    private boolean isExist;
    private boolean option = false;

    public static LinkedHashMap<String, MyTaintValList<String>> initValtMap = new LinkedHashMap<>();
    public static LinkedHashMap<String, LinkedHashSet<String>> initValLineMap = new LinkedHashMap();
    public static CallGraph cg = null;
    public static LinkedHashMap<String, LinkedHashSet<String>> taintValMap = new LinkedHashMap<>();
    public static LinkedHashMap<String, LinkedHashSet<Integer>> taintValLineMap = new LinkedHashMap<>();
    public static LinkedHashMap<String, Boolean> taintRetMap = new LinkedHashMap<>();
    public static LinkedHashMap<String, Boolean> taintClassMap = new LinkedHashMap<>();
    public static HashMap<String, HashSet<String>> fieldValMap = new LinkedHashMap<>();
    public static LinkedHashMap<SootClass, SootClass> abstractMap = new LinkedHashMap<>();
    private static final int CIRCLE_COUNT = 10;
    private static Hierarchy hierarchy;
    public static Stack<SootMethod> path = new Stack<SootMethod>();
    private static SootMethod path_method;
    private static final Logger LOGGER = LoggerFactory.getLogger(DataFlowAnalysis.class);
    private static List<String> currentPath = new ArrayList<>();
    private static Set<String> hasRepeatedPath = new HashSet<>();

    public DataFlowAnalysis(CallGraph cg) {
        this.cg = cg;
    }

    public boolean isDataFlowExist(String variable, Stack<SootMethod> path, HashSet<Integer> indexSet, boolean option) {
        this.isExist = false;
        this.variable = variable;
        this.indexSet = (HashSet<Integer>) indexSet.clone();
        this.option = option;
        this.path = (Stack<SootMethod>) path.clone();
        this.hierarchy = Scene.v().getActiveHierarchy();

        fieldValMap.clear();
        initValtMap.clear();
        taintValMap.clear();
        taintRetMap.clear();
        taintClassMap.clear();

        for (int i = 0; i < path.size(); i++) {
            SootMethod sootMethod = path.get(i);
            initValtMap.put(sootMethod.getSignature(),new MyTaintValList<String>());
        }

        for (int i = 0; i < path.size(); i++) {
            currentPath.clear();
            hasRepeatedPath.clear();
            try {
                if (!intraprocedural(path.get(i), path, new MyTaintValList<>(), new LinkedHashSet<Integer>(), true)) {
                    break;
                }
            } catch (Exception e1) {
                LOGGER.error(this.path.toString());
                for (SootMethod sm : this.path) {
                    try {
                        LOGGER.error(sm.retrieveActiveBody().toString());
                    } catch (Exception e2) {
                    }

                }
            }
        }
        return isExist;
    }

    public boolean intraprocedural(SootMethod sootMethod,Stack<SootMethod> path,
                                   MyTaintValList<String> taintValList,
                                   LinkedHashSet<Integer> taintValLineList, boolean b) {

        if(b == true){
            path_method = sootMethod;
        }
        boolean inSinkMethodSet = false;
        boolean isEntryMethod = false;
        if (sootMethod.getSignature().equals(path.get(0).getSignature())) {
            isEntryMethod = true;
        }

        LinkedHashMap<String, LinkedHashSet<String>> fieldTrackMap = new LinkedHashMap<>();
        Body body = null;
        if (sootMethod.hasActiveBody()) {
            body = sootMethod.retrieveActiveBody();
        }

        Stmt preStmt = null;
        if(body != null){
            for (Unit unit : body.getUnits()) {
                Stmt stmt = (Stmt) unit;
                if (stmt instanceof IdentityStmt && isEntryMethod) {
                    String key = sootMethod.getSignature();
                    taintValList.add(variable);
                    initValtMap.put(key, taintValList);
                    taintValList = initValtMap.get(key);
                }
                else if (stmt instanceof IdentityStmt && (!isEntryMethod)) {
                    if (((IdentityStmt) stmt).getLeftOp().toString().contains("this")) {
                        continue;
                    } else {
                        if(b == true){
                            SootMethod psm = path.get(path.indexOf(sootMethod) - 1);
                            HashSet<String> pTaintValList = taintValMap.get(psm.getSignature());
                            locateMethodInitTaintVal(psm, sootMethod, pTaintValList, taintValList);
                            initValtMap.put(sootMethod.getSignature(),taintValList);
                            if (taintValList.size() == 0) {
                                return false;
                            }
                        }
                    }
                }
                else if (stmt instanceof AssignStmt) {
                    Value rightOp = ((AssignStmt) stmt).getRightOp();
                    Value leftOp = ((AssignStmt) stmt).getLeftOp();

                    if (stmt.containsInvokeExpr()) {
                        SootMethod nSootMethod = calculateNextMethod(stmt, sootMethod);

                        if (nSootMethod == null) {
                            nSootMethod = calculateNextMethodLwh(stmt, sootMethod);
                            if (nSootMethod.getDeclaringClass().isInterface()) {
                                List<ValueBox> useBoxes = ((AssignStmt) stmt).getRightOp().getUseBoxes();

                                ValueBox leftOpBox = ((AssignStmt) stmt).getLeftOpBox();
                                if (useBoxes.size() == 0) {
                                } else {
                                    for (ValueBox useBox : useBoxes) {
                                        String valueBoxStr = useBox.getValue().toString();
                                        if(taintValList.contains(valueBoxStr)){
                                            taintValList.add(leftOpBox.getValue().toString());
                                            break;
                                        }
                                    }
                                }
                            }
                        }

                        SootMethod backMethod = stmt.getInvokeExpr().getMethod();
                        String sink2 = backMethod.getDeclaringClass().getName()+": "+backMethod.getName();

                        String cname = nSootMethod.getDeclaringClass().getName();
                        String mname = nSootMethod.getName();
                        String sink = cname + ": " + mname;
                        String sink_method = path.get(path.size() - 1).getDeclaringClass().getName() + ": " + path.get(path.size() - 1).getName();
                        inSinkMethodSet = false;
                        if (sink_method.equals(sink)||sink_method.equals(sink2)) {
                            List<Value> args = stmt.getInvokeExpr().getArgs();
                            Object[] tmp_args = args.toArray();
                            Object[] tmp_taintValList = taintValList.toArray();
                            int count = 0;
                            if (indexSet.contains(-1)) {
                                indexSet.remove(-1);
                                for (int i = 0; i < tmp_args.length; i++) {
                                    indexSet.add(i);
                                }
                                for (int i = 0; i < tmp_args.length; i++) {
                                    for (int j = 0; j < taintValList.size(); j++) {
                                        if ((tmp_taintValList[j].toString()).equals(tmp_args[i].toString())) {
                                            if (indexSet.contains(i)) {
                                                isExist = true;
                                            }
                                        }
                                    }
                                }
                            }
                            else{
                                for (int i = 0; i < tmp_args.length; i++) {
                                    for (int j = 0; j < taintValList.size(); j++) {
                                        if ((tmp_taintValList[j].toString()).equals(tmp_args[i].toString())) {
                                            if (indexSet.contains(i)) {
                                                count++;
                                            }
                                        }
                                    }
                                }
                                if (count == indexSet.size()) {
                                    isExist = true;
                                }
                            }

                            inSinkMethodSet = true;
                        }
                        if (nSootMethod != null
                                && (path.get(path.size() - 1).equals(nSootMethod))) {
                            calculateTypeOneDataFlow(sootMethod,
                                    nSootMethod, taintValList, taintValLineList,
                                    stmt, fieldTrackMap, false);

                        }else if (nSootMethod != null
                                && nSootMethod.getDeclaringClass().isInterface()
                                && (nSootMethod.getName().startsWith("insert")
                                || nSootMethod.getName().startsWith("update")
                                || "save".equals(nSootMethod.getName()))) {
                            calculateTypeOneDataFlow(sootMethod, nSootMethod,
                                    taintValList, taintValLineList, stmt,
                                    fieldTrackMap, false);

                        } else if (nSootMethod != null
                                && nSootMethod.getDeclaringClass().isJavaLibraryClass()
                                && nSootMethod.getDeclaringClass().isLibraryClass()
                                && !isRemoveMethod(nSootMethod)) {
                            calculateTypeTwoDataFlow(taintValList, taintValLineList,
                                    stmt, rightOp, leftOp, fieldTrackMap);

                        } else if (nSootMethod != null
                                && !nSootMethod.getDeclaringClass().isJavaLibraryClass()
                                && !nSootMethod.getDeclaringClass().isLibraryClass()
                                && !nSootMethod.isPhantom() && !isRemoveMethod(nSootMethod)) {
                            hierarchy = Scene.v().getActiveHierarchy();
                            if (isRelationToJavaClass(
                                    hierarchy, nSootMethod)) {

                                calculateTypeTwoDataFlow(taintValList, taintValLineList,
                                        stmt, rightOp, leftOp, fieldTrackMap);

                            } else {
                                calculateTypeFourDataFlow(sootMethod, taintValList,
                                        taintValLineList, (AssignStmt) stmt, fieldTrackMap);
                            }

                            MyTaintValList<String> nTaintValList = calculateInitVal(stmt, sootMethod,
                                    nSootMethod, taintValList);
                            String nextMethodSig = nSootMethod.getSignature();

                            if (nTaintValList != null) {
                                MyTaintValList<String> tmpSet = initValtMap.getOrDefault(
                                        nextMethodSig, new MyTaintValList<>());
                                tmpSet.addAll((LinkedHashSet<String>) nTaintValList.clone());
                                initValtMap.put(nextMethodSig, tmpSet);
                                String key = sootMethod.getSignature();
                                taintValLineMap.put(key, taintValLineList);
                                taintValMap.put(key, taintValList);

                                if((path.indexOf(path_method) + 1)<path.size()
                                        && nSootMethod != path.get(path.indexOf(path_method) + 1)
                                        && sootMethod.getDeclaringClass().isApplicationClass()
                                        && !nSootMethod.getSignature().equals(sootMethod.getSignature())){
                                    intraprocedural(nSootMethod, path, nTaintValList, new LinkedHashSet<Integer>(), false);
                                }

                                if (taintRetMap.containsKey(nextMethodSig)
                                        && taintRetMap.get(nextMethodSig)) {
                                    taintRetMap.remove(nextMethodSig);
                                    if (leftOp.getUseBoxes().size() == 0) {
                                        taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                                        taintValList.add(leftOp.toString());
                                    } else {
                                        for (ValueBox lValueBox : leftOp.getUseBoxes()) {
                                            if (lValueBox instanceof JimpleLocalBox
                                                    && (!("this".equals(lValueBox.getValue().toString())))) {
                                                taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                                                taintValList.add(lValueBox.getValue().toString());
                                            }
                                        }
                                    }
                                }
                            } else {
                                continue;
                            }
                        } else {
                            continue;
                        }
                    } else {
                        if (stmt.containsFieldRef()) {
                            SootField sootField = null;
                            String cName = null;
                            LinkedHashSet<String> fieldTrack = null;
                            String fieldVal = "";
                            if (rightOp instanceof JInstanceFieldRef) {
                                sootField = ((FieldRef) rightOp).getField();
                                cName = sootField.getDeclaringClass().getName();
                                fieldVal = rightOp.toString();
                                fieldTrack = fieldTrackMap.get(rightOp.toString());

                                if (fieldTrack == null) {
                                    fieldTrack = new LinkedHashSet<>();
                                    fieldTrack.add(rightOp.toString());
                                }

                                if (leftOp.getUseBoxes().size() == 0) {
                                    fieldTrack.add(leftOp.toString());

                                } else {
                                    for (ValueBox lValueBox : leftOp.getUseBoxes()) {
                                        if (lValueBox instanceof JimpleLocalBox
                                                && (!("this".equals(lValueBox.getValue().toString())))) {
                                            fieldTrack.add(lValueBox.getValue().toString());
                                        }
                                    }
                                }

                                fieldTrackMap.put(rightOp.toString(), fieldTrack);

                            } else if (leftOp instanceof JInstanceFieldRef) {
                                sootField = ((FieldRef) leftOp).getField();
                                cName = sootField.getDeclaringClass().getName();
                                fieldTrack = fieldTrackMap.get(leftOp.toString());
                                fieldVal = leftOp.toString();

                                if (fieldTrack == null) {
                                    fieldTrack = new LinkedHashSet<>();
                                    fieldTrack.add(leftOp.toString());
                                }

                                if (rightOp.getUseBoxes().size() == 0) {
                                    fieldTrack.add(rightOp.toString());

                                } else {
                                    for (ValueBox rValueBox : rightOp.getUseBoxes()) {
                                        if (rValueBox instanceof JimpleLocalBox) {
                                            fieldTrack.add(rValueBox.getValue().toString());
                                        }
                                    }
                                }

                                fieldTrackMap.put(leftOp.toString(), fieldTrack);
                            }

                            if (fieldTrack != null) {
                                LinkedHashSet<String> tmp = (LinkedHashSet<String>) fieldTrack.clone();
                                tmp.retainAll(taintValList);
                                if (tmp.size() != 0) {
                                    taintValList.addAll(fieldTrack);
                                    HashSet<String> fieldValSet = fieldValMap.get(cName);
                                    if (fieldValSet == null) fieldValSet = new LinkedHashSet<>();
                                    fieldValSet.add(fieldVal);
                                    fieldValMap.put(cName, fieldValSet);
                                    taintClassMap.put(sootMethod.getSignature(), true);
                                }
                            }

                        }

                        calculateTypeTwoDataFlow(taintValList, taintValLineList,
                                stmt, rightOp, leftOp, fieldTrackMap);
                    }

                }
                else if (stmt instanceof InvokeStmt) {
                    SootMethod nSootMethod = stmt.getInvokeExpr().getMethod();
                    String cname = nSootMethod.getDeclaringClass().getName();
                    String mname = nSootMethod.getName();
                    String sink = cname + ": " + mname;
                    String sink_method = path.get(path.size() - 1).getDeclaringClass().getName() + ": " + path.get(path.size() - 1).getName();
                    inSinkMethodSet = false;
                    if (sink_method.equals(sink)) {
                        List<Value> args = stmt.getInvokeExpr().getArgs();
                        Object[] tmp_args = args.toArray();
                        Object[] tmp_taintValList = taintValList.toArray();
                        int count = 0;
                        if (indexSet.contains(-1)) {
                            indexSet.remove(-1);
                            for (int i = 0; i < tmp_args.length; i++) {
                                indexSet.add(i);
                            }
                            for (int i = 0; i < tmp_args.length; i++) {
                                for (int j = 0; j < taintValList.size(); j++) {
                                    if ((tmp_taintValList[j].toString()).equals(tmp_args[i].toString())) {
                                        if (indexSet.contains(i)) {
                                            isExist = true;
                                        }
                                    }
                                }
                            }
                        }
                        else{
                            for (int i = 0; i < tmp_args.length; i++) {
                                for (int j = 0; j < taintValList.size(); j++) {
                                    if ((tmp_taintValList[j].toString()).equals(tmp_args[i].toString())) {
                                        if (indexSet.contains(i)) {
                                            count++;
                                        }
                                    }
                                }
                            }
                            if (count == indexSet.size()) {
                                isExist = true;
                            }
                        }

                        inSinkMethodSet = true;
                    }

                    if (nSootMethod != null
                            && (path.get(path.size() - 1).equals(nSootMethod))) {
                        calculateTypeOneDataFlow(sootMethod,
                                nSootMethod, taintValList, taintValLineList,
                                stmt, fieldTrackMap, false);

                    } else if (nSootMethod != null
                            && nSootMethod.getDeclaringClass().isInterface()
                            && (nSootMethod.getName().startsWith("insert")
                            || nSootMethod.getName().startsWith("update")
                            || nSootMethod.getName().equals("save"))) {
                        calculateTypeOneDataFlow(sootMethod,
                                nSootMethod, taintValList, taintValLineList,
                                stmt, fieldTrackMap, false);

                    } else if (nSootMethod != null
                            && nSootMethod.getDeclaringClass().isJavaLibraryClass()
                            && nSootMethod.getDeclaringClass().isLibraryClass()
                            && !isRemoveMethod(nSootMethod)) {
                        calculateTypeThreeDataFlow(taintValList,
                                taintValLineList, stmt, fieldTrackMap);
                        continue;
                    } else if (nSootMethod != null
                            && !nSootMethod.getDeclaringClass().isJavaLibraryClass()
                            && !nSootMethod.getDeclaringClass().isLibraryClass()
                            && !nSootMethod.isPhantom() && !isRemoveMethod(nSootMethod)) {
                        MyTaintValList<String> nTaintValList = calculateInitVal(stmt,
                                sootMethod, nSootMethod, taintValList);
                        if (nTaintValList != null) {
                            MyTaintValList<String> tmpSet = initValtMap.getOrDefault(
                                    nSootMethod.getSignature(), new MyTaintValList<>());

                            tmpSet.addAll((LinkedHashSet<String>) nTaintValList.clone());
                            initValtMap.put(nSootMethod.getSignature(), tmpSet);
                            String key = sootMethod.getSignature();
                            taintValLineMap.put(key, taintValLineList);
                            taintValMap.put(key, taintValList);

                            if((path.indexOf(path_method) + 1)<path.size()
                                    && nSootMethod != path.get(path.indexOf(path_method) + 1)
                                    && sootMethod.getDeclaringClass().isApplicationClass()
                                    && !nSootMethod.getSignature().equals(sootMethod.getSignature())){
                                if (!path.contains(nSootMethod)) {
                                    int index = currentPath.indexOf(nSootMethod.toString());
                                    if (index == -1) {
                                        currentPath.add(nSootMethod.toString());
                                        intraprocedural(nSootMethod, path, nTaintValList, new LinkedHashSet<Integer>(), false);

                                    } else {
                                        String subList = currentPath.subList(index, currentPath.size()).toString();
                                        if (!hasRepeatedPath.contains(subList)) {
                                            hasRepeatedPath.add(subList);
                                            intraprocedural(nSootMethod, path, nTaintValList, new LinkedHashSet<Integer>(), false);
                                        }
                                    }
                                } else {
                                    intraprocedural(nSootMethod, path, nTaintValList, new LinkedHashSet<Integer>(), false);
                                }
                            }
                            if (taintClassMap.containsKey(nSootMethod.getSignature())
                                    && taintClassMap.get(nSootMethod.getSignature())) {
                                taintClassMap.remove(nSootMethod.getSignature());

                                if ("<init>".equals(nSootMethod.getName())
                                        || nSootMethod.getName().startsWith("set")) {
                                    calculateTypeThreeDataFlow(taintValList,
                                            taintValLineList, stmt, fieldTrackMap);
                                }
                                if (isRelationToJavaClass(
                                        hierarchy, nSootMethod)) {
                                    calculateTypeThreeDataFlow(taintValList,
                                            taintValLineList, stmt, fieldTrackMap);
                                }
                            }
                        } else {
                            continue;
                        }
                    }
                }
                else if (stmt instanceof ReturnStmt) {
                    ReturnStmt rStmt = (ReturnStmt) stmt;
                    if (rStmt.getOpBox() != null) {
                        if (rStmt.getOp().getUseBoxes().size() == 0) {

                            if (taintValList.contains(
                                    rStmt.getOpBox().getValue().toString())) {

                                if (onlyReturn(path, sootMethod)) {
                                    calculateReturn(sootMethod,
                                            taintValList, taintValLineList);

                                } else {
                                    taintRetMap.put(sootMethod.getSignature(), true);
                                }
                            }
                        } else {
                            for (ValueBox valueBox : rStmt.getOp().getUseBoxes()) {
                                String valueBoxStr = valueBox.getValue().toString();

                                if (valueBoxStr.startsWith("\"")
                                        || valueBoxStr.startsWith("\'")
                                        || isNumeric(valueBoxStr)) {
                                } else if (taintValList.contains(valueBoxStr)) {
                                    if (onlyReturn(path, sootMethod)) {
                                        calculateReturn(sootMethod, taintValList, taintValLineList);
                                    } else {
                                        taintRetMap.put(sootMethod.getSignature(), true);
                                    }
                                }
                            }
                        }
                    }
                }
                else if(stmt instanceof JIfStmt){
                    JIfStmt jIfStmt = (JIfStmt) stmt;
                    if(preStmt.toString().contains("equals") && preStmt instanceof AssignStmt){//equals  ->  ==
                        Value rightOp = ((AssignStmt) preStmt).getRightOp();
                        List<ValueBox> useBoxes = rightOp.getUseBoxes();
                        if(taintValList.contains(useBoxes.get(0).getValue().toString())){
                            taintValList.add(useBoxes.get(1).getValue().toString());
                        }
                        else if(taintValList.contains(useBoxes.get(1).getValue().toString())){
                            taintValList.add(useBoxes.get(0).getValue().toString());
                        }
                    }
                    else{//==  ->  !=    //!=  ->  ==
                        List<ValueBox> useBoxes = jIfStmt.getConditionBox().getValue().getUseBoxes();
                        if(taintValList.contains(useBoxes.get(0).getValue().toString())){
                            taintValList.add(useBoxes.get(1).getValue().toString());
                        }
                        else if(taintValList.contains(useBoxes.get(1).getValue().toString())){
                            taintValList.add(useBoxes.get(0).getValue().toString());
                        }
                    }
                }
                preStmt = stmt;
            }
        }

        String key = sootMethod.getSignature();
        taintValLineMap.put(key, taintValLineList);
        taintValMap.put(key, taintValList);
        if (inSinkMethodSet == true) {
            return false;
        }
        return true;
    }

    private SootMethod calculateNextMethodLwh(Stmt stmt, SootMethod sootMethod) {
        SootMethod nSootMethod = stmt.getInvokeExpr().getMethod();
        Iterator iterator = cg.edgesOutOf(sootMethod);
        while (iterator.hasNext()) {
            Edge edge = (Edge) iterator.next();
            if (edge.srcStmt().equals(stmt)) {
                nSootMethod = edge.tgt();
            }
        }

        return nSootMethod;
    }

    private static void calculateTypeFourDataFlow(
            SootMethod sootMethod, LinkedHashSet<String> taintValList,
            LinkedHashSet<Integer> taintValLineList,
            AssignStmt stmt, LinkedHashMap<String,
            LinkedHashSet<String>> fieldTrackMap) {
        fieldTrackIsTaint(taintValList, fieldTrackMap);

        boolean flag = false;
        Value leftOp = stmt.getLeftOp();
        Value rightOp = stmt.getRightOp();

        for (ValueBox rValueBox : rightOp.getUseBoxes()) {
            String rValueBoxStr = rValueBox.getValue().toString();
            if (rValueBoxStr.startsWith("\"")
                    || rValueBoxStr.startsWith("\'")
                    || isNumeric(rValueBoxStr)) {
                continue;

            } else if (taintValList.contains(rValueBoxStr)
                    && initValtMap.get(sootMethod.getSignature()).contains(rValueBoxStr)
                    && rValueBox.getValue() instanceof JimpleLocal) {
                flag = true;
                break;
            }
        }
        if (flag) {

            if (leftOp.getUseBoxes().size() == 0) {
                taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                taintValList.add(leftOp.toString());

            } else {
                for (ValueBox lValueBox : leftOp.getUseBoxes()) {
                    if (lValueBox instanceof JimpleLocalBox
                            && (!("this".equals(lValueBox.getValue().toString())))) {

                        taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                        taintValList.add(lValueBox.getValue().toString());
                    }
                }
            }
        }
    }

    private static void calculateTypeThreeDataFlow(
            LinkedHashSet<String> taintValList,
            LinkedHashSet<Integer> taintValLineList, Stmt stmt,
            LinkedHashMap<String, LinkedHashSet<String>> fieldTrackMap) {
        fieldTrackIsTaint(taintValList, fieldTrackMap);

        boolean flag = false;
        for (ValueBox valueBox : stmt.getInvokeExprBox().getValue().getUseBoxes()) {
            if (valueBox instanceof ImmediateBox &&
                    taintValList.contains(valueBox.getValue().toString())) {
                flag = true;
            }
            if (flag && valueBox instanceof JimpleLocalBox) {
                taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                taintValList.add(valueBox.getValue().toString());
            }
        }
    }

    private static void calculateTypeTwoDataFlow(
            LinkedHashSet<String> taintValList,
            LinkedHashSet<Integer> taintValLineList,
            Stmt stmt, Value rightOp, Value leftOp,
            LinkedHashMap<String, LinkedHashSet<String>> fieldTrackMap) {
        fieldTrackIsTaint(taintValList, fieldTrackMap);

        if (rightOp.getUseBoxes().size() == 0
                && taintValList.contains(rightOp.toString())) {

            if (leftOp.getUseBoxes().size() == 0) {
                taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                taintValList.add(leftOp.toString());

            } else {
                for (ValueBox lValueBox : leftOp.getUseBoxes()) {
                    if (lValueBox instanceof JimpleLocalBox
                            && (!("this".equals(lValueBox.getValue().toString())))) {
                        taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                        taintValList.add(lValueBox.getValue().toString());
                    }
                }
            }
        } else if (rightOp.getUseBoxes().size() != 0) {
            for (ValueBox rValueBox : rightOp.getUseBoxes()) {
                String rValueBoxStr = rValueBox.getValue().toString();

                if (rValueBoxStr.startsWith("\"")
                        || rValueBoxStr.startsWith("\'")
                        || isNumeric(rValueBoxStr)) {

                } else if (taintValList.contains(rValueBoxStr)) {

                    if (leftOp.getUseBoxes().size() == 0) {
                        taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                        taintValList.add(leftOp.toString());

                    } else {
                        for (ValueBox lValueBox : leftOp.getUseBoxes()) {
                            if (lValueBox instanceof JimpleLocalBox
                                    && (!("this".equals(lValueBox.getValue().toString())))) {

                                taintValLineList.add(stmt.getJavaSourceStartLineNumber());
                                taintValList.add(lValueBox.getValue().toString());
                            }
                        }
                    }
                }
            }
        }
    }

    private static void calculateTypeOneDataFlow(
            SootMethod sootMethod, SootMethod nSootMethod,
            LinkedHashSet<String> taintValList,
            LinkedHashSet<Integer> taintValLineList, Stmt stmt,
            LinkedHashMap<String, LinkedHashSet<String>> fieldTrackMap,
            boolean isAbstractLibraryMethod) {
        fieldTrackIsTaint(taintValList, fieldTrackMap);
        List<ValueBox> useBoxes = null;
        String stmtStr = stmt.toString();

        if (stmt instanceof AssignStmt) {
            useBoxes = ((AssignStmt) stmt).getRightOp().getUseBoxes();
            stmtStr = ((AssignStmt) stmt).getRightOp().toString();

        } else if (stmt instanceof InvokeStmt) {
            useBoxes = stmt.getUseBoxes();
        }

        if (useBoxes.size() == 0 && taintValList.contains(stmtStr)) {

            String key = sootMethod.getSignature();
            taintValLineMap.put(key, taintValLineList);
            taintValMap.put(key, taintValList);
        } else if (useBoxes.size() != 0) {
            for (ValueBox valueBox : useBoxes) {
                String valueBoxStr = valueBox.getValue().toString();
                if (valueBoxStr.startsWith("\"")
                        || valueBoxStr.startsWith("\'")
                        || isNumeric(valueBoxStr)) {

                } else if (taintValList.contains(valueBoxStr)) {
                    String key = sootMethod.getSignature();
                    taintValLineMap.put(key, taintValLineList);
                    taintValMap.put(key, taintValList);
                }
            }
        }
    }

    private static void fieldTrackIsTaint(
            LinkedHashSet<String> taintValList,
            LinkedHashMap<String, LinkedHashSet<String>> fieldTrackMap) {

        Iterator LinkedHashSetIterator = fieldTrackMap.keySet().iterator();

        while (LinkedHashSetIterator.hasNext()) {
            String fieldValue = (String) LinkedHashSetIterator.next();
            LinkedHashSet<String> fieldTrack = fieldTrackMap.get(fieldValue);
            if (fieldTrack != null) {
                LinkedHashSet<String> tmp = (LinkedHashSet<String>) fieldTrack.clone();
                tmp.retainAll(taintValList);

                if (tmp.size() != 0) {
                    taintValList.addAll(fieldTrack);
                    String cName = fieldValue.split("<")[1].split(":")[0];
                    HashSet<String> fieldValSet = fieldValMap.get(cName);

                    if (fieldValSet == null)
                        fieldValSet = new LinkedHashSet<>();

                    fieldValSet.add(fieldValue.toString());
                    fieldValMap.put(cName, fieldValSet);
                }
            }
        }
    }

    private static MyTaintValList<String> calculateInitVal(
            Stmt stmt, SootMethod sootMethod,
            SootMethod nSootMethod,
            LinkedHashSet<String> taintValList) {
        LinkedHashSet<Integer> flags = new LinkedHashSet();
        MyTaintValList<String> nTaintValList = new MyTaintValList<>();

        for (int i = 0; i < stmt.getInvokeExpr().getArgs().size(); i++) {
            String arg = stmt.getInvokeExpr().getArg(i).toString();
            if (taintValList.contains(arg)) {
                flags.add(i);
            }
        }

        try {
            if (!isLibraryMethod(nSootMethod)) {
                HashSet<String> fieldVals = fieldValMap.get(
                        nSootMethod.getDeclaringClass().getName());

                if (fieldVals != null) {
                    Body body = nSootMethod.retrieveActiveBody();
                    for (ValueBox box : body.getUseAndDefBoxes()) {
                        if (fieldVals.contains(box.getValue().toString())) {
                            nTaintValList.add(box.getValue().toString());
                        }
                    }
                }
            }
        } catch (Exception e) {
        }

        if (flags.size() == 0 && nTaintValList.size() == 0)
            return null;

        try {
            Body body = nSootMethod.retrieveActiveBody();

            for (int i : flags) {
                String taintVal = body.getParameterLocal(i).toString();
                nTaintValList.add(taintVal);
            }

            if (nTaintValList.size() != 0) {
                for (int i = 0; i < nSootMethod.getParameterCount(); i++) {
                    if ("org.aspectj.lang.JoinPoint".equals(
                            nSootMethod.getParameterType(i).toString())) {
                        nTaintValList.add(body.getParameterLocal(i).getName());
                        break;
                    }
                }
            }

        } catch (Exception e) {
        }

        if (nTaintValList.size() == 0) {
            return null;
        }

        return nTaintValList;
    }



    private SootMethod calculateNextMethod(Stmt stmt, SootMethod sootMethod) {
        SootMethod nSootMethod = stmt.getInvokeExpr().getMethod();
        if (nSootMethod.getDeclaringClass().isInterface()) {
            Tag tag = nSootMethod.getDeclaringClass().getTag("VisibilityAnnotationTag");
            if (tag != null) {
                for (AnnotationTag annotationTag : ((VisibilityAnnotationTag)tag).getAnnotations()){
                    if(annotationTag.getType().equals("Lorg/apache/ibatis/annotations/Mapper;")){
                        return null;
                    }
                }
            }
            Iterator iterator = cg.edgesOutOf(sootMethod);
            while (iterator.hasNext()) {
                Edge edge = (Edge) iterator.next();
                if (edge.srcStmt().equals(stmt)) {
                    nSootMethod = edge.tgt();
                }
            }
        }

        return nSootMethod;
    }

    public static boolean onlyReturn(Stack<SootMethod> path, SootMethod sootMethod) {
        Sources sources = new Sources(cg.edgesInto(sootMethod));

        if (path.size() == 1) {
            return true;
        }
        while (sources.hasNext()) {
            if (path.get(path.size() - 2).equals(sources.next().method())) {
                return false;
            }
        }

        return true;
    }

    private static void calculateReturn(
            SootMethod sootMethod,
            LinkedHashSet<String> taintValList,
            LinkedHashSet<Integer> taintValLineList) {

        Iterator<Edge> iterator = cg.edgesInto(sootMethod);
        while (iterator.hasNext()) {
            LinkedHashSet<String> hashSet = new LinkedHashSet();
            Edge edge = iterator.next();
            if (path.contains(edge.getSrc().method()) || path.size() >= CIRCLE_COUNT) {
                continue;
            }
            if (edge.srcStmt() instanceof JAssignStmt) {
                Stmt rStmt = edge.srcStmt();
                if (((JAssignStmt) rStmt).getLeftOp().getUseBoxes().size() == 0) {
                    hashSet.add(((JAssignStmt) rStmt).getLeftOp().toString());
                } else {
                    for (ValueBox rValueBox : ((JAssignStmt) rStmt).getLeftOp().getUseBoxes()) {
                        if (rValueBox.getValue().toString().startsWith("\"")
                                || rValueBox.getValue().toString().startsWith("\'")
                                || isNumeric(rValueBox.getValue().toString())) {
                            continue;
                        } else {
                            hashSet.add(rValueBox.getValue().toString());
                        }
                    }
                }

                try {
                    if (!isLibraryMethod(edge.getSrc().method())) {
                        HashSet<String> fieldVals = fieldValMap.get(edge.getSrc().method().getDeclaringClass().getName());
                        if (fieldVals != null) {
                            Body tmp = edge.getSrc().method().retrieveActiveBody();
                            for (ValueBox box : tmp.getUseAndDefBoxes()) {
                                if (fieldVals.contains(box.getValue().toString())) {
                                    hashSet.add(box.getValue().toString());
                                }
                            }
                        }
                    }
                } catch (Exception e) {

                }
            }
            MyTaintValList<String> tmpSet = initValtMap.getOrDefault(edge.getSrc().method().getSignature(), new MyTaintValList<>());
            tmpSet.addAll((LinkedHashSet<String>) hashSet.clone());
            initValtMap.put(edge.getSrc().method().getSignature(), tmpSet);
            String key = sootMethod.getSignature();
            taintValLineMap.put(key, taintValLineList);
            taintValMap.put(key, taintValList);
        }
    }

    public static boolean isLibraryMethod(SootMethod sootMethod) {
        SootClass sootClass = sootMethod.getDeclaringClass();
        return Scene.v().getLibraryClasses().contains(sootClass);
    }

    public static boolean isNumeric(String str) {
        Pattern pattern = Pattern.compile("[0-9]*");
        Matcher isNum = pattern.matcher(str);
        if (!isNum.matches()) {
            return false;
        }
        return true;
    }

    public static boolean isRemoveMethod(SootMethod sootMethod) {
        if (sootMethod.getName().contains("remove") || sootMethod.getName().contains("delete")) {
            return true;
        }
        return false;
    }

    public static boolean isRelationToJavaClass(Hierarchy hierarchy, SootMethod sootMethod) {
        if (sootMethod.getDeclaringClass().isInterface()) {
            List<SootClass> classList = hierarchy.getSuperinterfacesOf(sootMethod.getDeclaringClass());
            for (SootClass sc : classList) {
                if (!"java.lang.Object".equals(sc.getName()) && sc.isJavaLibraryClass()) {
                    return true;
                }
            }
            return false;
        }

        List<SootClass> scl = hierarchy.getSuperclassesOf(sootMethod.getDeclaringClass());
        for (SootClass sc : scl) {
            if (!"java.lang.Object".equals(sc.getName()) && sc.isJavaLibraryClass()) {
                return true;
            }
        }

        Chain<SootClass> il = sootMethod.getDeclaringClass().getInterfaces();
        for (SootClass sc : il) {
            if (sc.isJavaLibraryClass()) {
                return true;
            }
        }

        return false;
    }

    private void locateMethodInitTaintVal(SootMethod psm, SootMethod sm, HashSet<String> pTaintValList, HashSet<String> taintValList) {
        Iterator<Edge> edgeIterator = cg.edgesOutOf(psm);
        HashSet<Character> flags = new HashSet();
        while (edgeIterator.hasNext()) {
            Edge edge = edgeIterator.next();
            if (edge.getSrc().equals(psm) && edge.getTgt().equals(sm)) {
                Stmt invokeStmt = edge.srcStmt();
                for (int i = 0; i < invokeStmt.getInvokeExpr().getArgs().size(); i++) {
                    String arg = invokeStmt.getInvokeExpr().getArg(i).toString();
                    if (pTaintValList.contains(arg)) {
                        flags.add((char) (i + '0'));
                    }
                }
            }
        }

        Body body = sm.retrieveActiveBody();
        for (Unit unit : body.getUnits()) {
            Stmt stmt = (Stmt) unit;
            if (stmt instanceof IdentityStmt && !stmt.toString().contains("this")) {
                char argIndex = ((IdentityStmt) stmt).getRightOp().toString().charAt(10);
                if (flags.contains(argIndex)) {
                    String arg = ((IdentityStmt) stmt).getLeftOp().toString();
                    taintValList.add(arg);
                }
            }
        }
    }
}


