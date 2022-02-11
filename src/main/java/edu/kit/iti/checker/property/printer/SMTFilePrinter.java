package edu.kit.iti.checker.property.printer;

import edu.kit.iti.checker.property.checker.PropertyChecker;
import edu.kit.iti.checker.property.lattice.PropertyAnnotation;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

public class SMTFilePrinter extends PrintWriter {

    protected PropertyChecker checker;
    protected String varName;

    Map<String, PropertyAnnotationType> annotationTypes = new HashMap<>();

    public SMTFilePrinter(BufferedWriter outS, PropertyChecker checker, String varName) {
        super(outS);
        this.checker = checker;
        this.varName = varName;
        for (BaseTypeChecker typeChecker : this.checker.getSubcheckers()) {
            LatticeAnnotatedTypeFactory lf = (LatticeAnnotatedTypeFactory) typeChecker.getTypeFactory();
            this.annotationTypes.putAll(lf.getLattice().getAnnotationTypes());
        }
        print("(set-logic QF_UFNIA)");
        println();

    }

    public SMTFilePrinter(File file, PropertyChecker checker, String varName) throws FileNotFoundException {
        super(file);
        this.checker = checker;
        this.varName = varName;
        for (BaseTypeChecker typeChecker : this.checker.getSubcheckers()) {
            LatticeAnnotatedTypeFactory lf = (LatticeAnnotatedTypeFactory) typeChecker.getTypeFactory();
            this.annotationTypes.putAll(lf.getLattice().getAnnotationTypes());
        }
        print("(set-logic QF_UFLIA)");
        println();
    }

    public void printLine(String line) {
        if (line.contains("assert")) {
            print(line);
            println();
        } else if (line.contains("@")) {
            printProperty(line);
        }
    }

    public void printProperty(String prop) {
        String ident = getAnnoIdent(prop);
        //ArrayList<String> pNames = getAnnoParamNames(prop);
        //getParameterNames(ident);
        ArrayList<String> pNames = getParameterNames(ident);
        ArrayList<String> passedParams = new ArrayList<String>();
        getPassedParams(prop, passedParams);
        String varName = getVarName(prop);
        ArrayList<String> properties = new ArrayList<String>();
        ArrayList<String> smtAnnos = new ArrayList<String>();

        if (annotationTypes.containsKey(ident)) {
            getPropertyFromAnntotation(annotationTypes.get(ident).toString(), properties);
        }

        for (String p : properties) {
            for (int i = 0; i < pNames.size(); i++) {
                p = replaceParams(p, pNames.get(i), passedParams.get(i));
            }
            if (p.contains("subject")) {
                p = replaceParams(p, "subject", varName);
            }
            String smtProp = toSMT(parseStringAnno(p));
            smtAnnos.add(smtProp);
        }

        if (!varName.equals(this.varName)) {
            for (String sa : smtAnnos) {
                print("(assert " + sa + ")");
                println();
            }
        } else {
            print("(assert (or ");
            for (String sa : smtAnnos) {
                print("(not " + sa + ") ");
            }
            print("))");
            println();
        }

    }

    private String getAnnoIdent(String prop) {
        return prop.substring(prop.indexOf("@") + 1, prop.indexOf("("));
    }

    private ArrayList<String> getAnnoParamNames(String prop) {
        ArrayList<String> paramNames = new ArrayList<String>();
        String paramString = prop.substring(prop.indexOf("(") + 1, prop.indexOf(")"));
        String [] s = paramString.split(", ");
        for (String s1 : s) {
            String pName = s1.split("=")[0];
            if (pName.contains(" ")) {
                pName.replaceAll(" ", "");
            }
            paramNames.add(pName);
        }
        return paramNames;
    }

    private void getPassedParams(String prop, ArrayList<String> passedParams) {
        if (prop.contains("\"")) {
            String s = prop.substring(prop.indexOf("\"") + 1);
            String rest = s.substring(s.indexOf("\"") + 1);
            s = s.substring(0, s.indexOf("\""));
            passedParams.add(s);
            getPassedParams(rest, passedParams);
        }
    }

    private String getVarName(String prop) {
        String [] ar =  prop.split(" ");
        return ar[ar.length - 1];
    }

    private void getPropertyFromAnntotation (String anno, ArrayList<String> properties) {
        ArrayList<String> listAnno = new ArrayList<String>();
        String[] s = anno.split(" ");
        for (String s1 : s) {
            listAnno.add(s1);
        }
        String property = "";
        String wfCond = "";
        if (listAnno.contains("<==>")) {
            int i = listAnno.indexOf("<==>") + 1;
            while (i < listAnno.size() && !listAnno.get(i).equals("for")) {
                property = property + listAnno.get(i) + " ";
                i++;
            }
            if (listAnno.get(i).equals("for")) {
                i++;
                while (i < listAnno.size()) {
                    wfCond = wfCond + listAnno.get(i) + " ";
                    i++;
                }
            }
        }
        properties.add(property);
        properties.add(wfCond);
    }

    private String replaceParams (String in, String pName, String p) {
        return in.replace("§" + pName + "§", p);
    }

    private ArrayList<String> parseStringAnno (String anno) {
        ArrayList<String> listAnno = new ArrayList<String>();
        String[] s = anno.split(" ");
        for (String s1 : s) {
//            System.out.println(s1);
            listAnno.add(s1);
        }
        return listAnno;
    }

    private String toSMT(ArrayList<String> parsedAnno) {
        String smt = "";
        if (parsedAnno.size() == 1) {
            smt = parsedAnno.get(0);
        }
        if (parsedAnno.contains("&&")) {
            smt = parseAnd(parsedAnno, "&&");
//            smt = "(and (" + toSMT(leftSide) + " " + toSMT(rightSide) + ")";
        }
        else if (parsedAnno.contains(">=")) {
            smt = parseAnd(parsedAnno, ">=");
//            smt = "(>= (" + toSMT(leftSide) + " " + toSMT(rightSide) + ")";
        } else if (parsedAnno.contains("<=")) {
            smt = parseAnd(parsedAnno, "<=");
        } else if (parsedAnno.contains(">")) {
            smt = parseAnd(parsedAnno, ">");
        } else if (parsedAnno.contains("<")) {
            smt = parseAnd(parsedAnno, "<");
        } else if (parsedAnno.contains("+")) {
            smt = parseAnd(parsedAnno, "+");
        } else if (parsedAnno.contains("-")) {
            smt = parseAnd(parsedAnno, "-");
        } else if (parsedAnno.contains("*")) {
            smt = parseAnd(parsedAnno, "*");
        } else if (parsedAnno.contains("/")) {
            smt = parseAnd(parsedAnno, "/");
        } else if (parsedAnno.contains("%")) {
            smt = parseAnd(parsedAnno, "%");
        }
        return  smt;
    }

    private String parseAnd (ArrayList<String> parsedAnno, String op) {
        int index = parsedAnno.indexOf(op);
        ArrayList<String> leftSide = new ArrayList<String>();
        ArrayList<String> rightSide = new ArrayList<String>();
        String lSide;
        String rSide;
        if (index - 1 > 0) {
            for (String s : parsedAnno.subList(0, index )) {
                leftSide.add(s);
            }
            lSide = toSMT(leftSide);
        } else {
            lSide = parsedAnno.get(0);
        }
        if (index + 1 < parsedAnno.size() - 1) {
            for (String s : parsedAnno.subList(index + 1, parsedAnno.size())) {
                rightSide.add(s);
            }
            rSide = toSMT(rightSide);
//            System.out.println(rSide);
        } else {
            rSide = parsedAnno.get(parsedAnno.size()-1);
//            System.out.println(rSide);
        }
        if (op.equals("&&")) {
            op = "and";
        }
        if (op.equals("/")) {
            op = "div";
        }
        if (op.equals("%")) {
            op = "mod";
        }
        return "(" + op + " " + lSide + " " + rSide + ")";
    }

    public void printAnnoToProve(PropertyAnnotation pa, String name) {
        println();
        String repParam = replacePropertyParameters(pa, name);
        String repSub = repParam.replace("§subject§", name);
        String repCond = replaceCondParameters(pa, name);
        String smtString = "(not " + toSMT(parseStringAnno(repSub)) + ")";
        String smtCond = "(not " + toSMT(parseStringAnno(repCond)) + ")";
        //print(smtCond);
        //println();
        //print(smtString);
        print("(assert (or " + smtString + " " + smtCond + "))");
        println();
    }

    private String replaceCondParameters(PropertyAnnotation pa, String name) {
        java.util.List<PropertyAnnotationType.Parameter> parL = pa.getAnnotationType().getParameters();
        java.util.List<String> acPar = pa.getActualParameters();
        String cond = "?";
        if (!parL.isEmpty()) {
            cond = pa.getAnnotationType().getWFCondition();
            //    System.out.println(pa.getName() + " " + pa.getAnnotationType().getProperty());
            //    System.out.println(pa.getAnnotationType().getWFCondition());
            for (int i = 0; i < parL.size(); i++) {
                String old = "§" + parL.get(i).getName() + "§";
                String act = acPar.get(i);
                cond = cond.replace(old, act);
            }
            cond = cond.replace("§subject§", name);
        }
        return cond;
    }

    private String replacePropertyParameters(PropertyAnnotation pa, String name) {
        java.util.List<PropertyAnnotationType.Parameter> parL = pa.getAnnotationType().getParameters();
        java.util.List<String> acPar = pa.getActualParameters();
        String prop = "?";
        if (!parL.isEmpty()) {
            prop = pa.getAnnotationType().getProperty();
            for (int i = 0; i < parL.size(); i++) {
                String old = "§" + parL.get(i).getName() + "§";
                String act = acPar.get(i);
                prop = prop.replace(old, act);
            }
            prop = prop.replace("§subject§", name);
        }
        return prop;
    }

    private ArrayList<String> getParameterNames(String ident) {
        ArrayList<String> pNames = new ArrayList<String>();
        //System.out.println("!!!!!!!" + annotationTypes);
        if (annotationTypes.containsKey(ident)) {
            String typeDef = annotationTypes.get(ident).toString();
            //System.out.println("!!!!!!!" + typeDef);
            String params = typeDef.substring(typeDef.indexOf("(") + 1, typeDef.indexOf(")"));
            //System.out.println("????????" + params);
            String[] splittedParams = params.split(", ");
            for (String s : splittedParams) {
                String[] typeAndName = s.split(" ");
                pNames.add(typeAndName[1]);
            }
        }
        //System.out.println("=======" + pNames);
        return pNames;
    }

}
