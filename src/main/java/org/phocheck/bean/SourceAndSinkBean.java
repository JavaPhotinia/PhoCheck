package org.phocheck.bean;

import soot.SootMethod;

import java.util.HashSet;
import java.util.Set;

public class SourceAndSinkBean {
    private SootMethod sourceMethod;
    private SootMethod SinkMethod;
    private Set<String> paths = new HashSet<>();

    public SootMethod getSourceMethod() {
        return sourceMethod;
    }

    public void setSourceMethod(SootMethod sourceMethod) {
        this.sourceMethod = sourceMethod;
    }

    public SootMethod getSinkMethod() {
        return SinkMethod;
    }

    public void setSinkMethod(SootMethod sinkMethod) {
        SinkMethod = sinkMethod;
    }

    public Set<String> getPath() {
        return paths;
    }

    public void setPath(Set<String> paths) {
        this.paths = paths;
    }

    public void addPath(String path) {
        this.paths.add(path);
    }
}
