package org.phocheck.analysis;

import java.util.LinkedHashSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MyTaintValList<T> extends LinkedHashSet<T> {
    @Override
    public boolean add(T t) {
        if(t instanceof String){
            String s = (String)t;
            if(s.equalsIgnoreCase("null")){
                return false;
            }
            if(isNumeric(s)){
                return false;
            }
        }
        return super.add(t);
    }
    public static boolean isNumeric(String str) {
        Pattern pattern = Pattern.compile("[0-9]*");
        Matcher isNum = pattern.matcher(str);
        if (!isNum.matches()) {
            return false;
        }
        return true;
    }
}
