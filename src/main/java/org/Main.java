package org;

import analysis.CreateEdge;
import org.phocheck.analysis.AccessControlTransformer;
import org.phocheck.utils.BenchmarksConfig;
import soot.*;
import soot.options.Options;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

public class Main {
    public static void main(String[] args) {
        String benchmark = "jeesite";
        initializeSoot(benchmark);
        CreateEdge createEdge = new CreateEdge();
        createEdge.initCallGraph("");
        Scene.v().setMainClass(CreateEdge.projectMainMethod.getDeclaringClass());

        Pack pack = PackManager.v().getPack("cg");
        pack.apply();

        pack = PackManager.v().getPack("wjtp");
        pack.add(new Transform("wjtp.ForwardTrans", new AccessControlTransformer()));
        pack.apply();
    }

    public static void initializeSoot(String benchmark) {
        G.reset();
        List<String> dir = BenchmarksConfig.getSourceProcessDir(benchmark);

        System.out.println(dir);
        Options.v().set_process_dir(dir);

        Options.v().setPhaseOption("cg.spark", "on");
        Options.v().setPhaseOption("cg.spark", "verbose:true");
        Options.v().setPhaseOption("cg.spark", "enabled:true");
        Options.v().setPhaseOption("cg.spark", "propagator:worklist");
        Options.v().setPhaseOption("cg.spark", "simple-edges-bidirectional:false");
        Options.v().setPhaseOption("cg.spark", "on-fly-cg:true");
        // Options.v().setPhaseOption("cg.spark", "pre-jimplify:true");
        Options.v().setPhaseOption("cg.spark", "double-set-old:hybrid");
        Options.v().setPhaseOption("cg.spark", "double-set-new:hybrid");
        Options.v().setPhaseOption("cg.spark", "set-impl:double");
        Options.v().setPhaseOption("cg.spark", "apponly:true");
        Options.v().setPhaseOption("cg.spark", "simple-edges-bidirectional:false");
        Options.v().set_verbose(true);

        // Options.v().setPhaseOption("cg.cha", "on");
        // Options.v().setPhaseOption("cg.cha", "enabled:true");
        // Options.v().setPhaseOption("cg.cha", "verbose:true");
        // Options.v().setPhaseOption("cg.cha", "apponly:true");

        List<String> includeList = new LinkedList<String>();
        // includeList.add("java.lang.*");
        // includeList.add("java.util.*");
        includeList.add("org.springframework.*");
        includeList.add("org.springframework.security.*");
        // includeList.add("java.io.");
        // includeList.add("java.security.");
        // includeList.add("javax.servlet.");
        // includeList.add("javax.crypto.");
        Options.v().set_include(includeList);

        Options.v().set_whole_program(true);

        Options.v().set_src_prec(Options.src_prec_class);

        Options.v().set_exclude(excludedPackages());
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_no_bodies_for_excluded(true);

        Options.v().set_keep_line_number(true);
        Options.v().set_soot_classpath(getSootClassPath(benchmark));
        Options.v().set_output_format(Options.output_format_jimple);
        Scene.v().loadNecessaryClasses();
        PhaseOptions.v().setPhaseOption("jb", "use-original-names:true");
    }

    private static String getSootClassPath(String benchmark) {
        String userdir = System.getProperty("user.dir");
        String javaHome = System.getProperty("java.home");
        if (javaHome == null || javaHome.equals(""))
            throw new RuntimeException("Could not get property java.home!");

        String sootCp = javaHome + File.separator + "lib" + File.separator + "rt.jar";
        //String sootCp = "F:/Java/jre" + File.separator + "lib" + File.separator + "rt.jar";
        sootCp += File.pathSeparator + javaHome + File.separator + "lib" + File.separator + "jce.jar";
        //sootCp += File.pathSeparator + "F:/Java/jre" + File.separator + "lib" + File.separator + "jce.jar";

        File file = new File(BenchmarksConfig.getDependencyDir(benchmark));
        File[] fs = file.listFiles();
        if(fs != null){
            for (File f : Objects.requireNonNull(fs)) {
                if (!f.isDirectory())
                    sootCp += File.pathSeparator + BenchmarksConfig.getDependencyDir(benchmark) + File.separator + f.getName();
            }
        }
        return sootCp;
    }

    private static List<String> excludedPackages() {
        List<String> excludedPackages = new ArrayList<>();
        excludedPackages.add("javax.swing.*");
        excludedPackages.add("java.awt.*");
        excludedPackages.add("sun.awt.*");
        excludedPackages.add("com.sun.java.swing.*");
        excludedPackages.add("reactor.*");
        excludedPackages.add("net.sf.cglib.*");
        excludedPackages.add("org.springframework.*");
        excludedPackages.add("org.apache.poi.*");
        excludedPackages.add("com.mysql.*");
        excludedPackages.add("org.ehcache.impl.internal.*");
        excludedPackages.add("ch.qos.*");
        excludedPackages.add("org.apache.*");
        excludedPackages.add("org.eclipse.*");
        excludedPackages.add("java.util.*");
        return excludedPackages;
    }
}
