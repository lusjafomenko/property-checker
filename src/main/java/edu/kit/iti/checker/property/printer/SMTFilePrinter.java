package edu.kit.iti.checker.property.printer;

import edu.kit.iti.checker.property.checker.PropertyChecker;
import edu.kit.iti.checker.property.lattice.PropertyAnnotation;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;

import java.io.BufferedWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

public class SMTFilePrinter extends PrintWriter {

    protected PropertyChecker checker;
    protected String varName;
    String enclClassName;
    String enclMethodName;
    String invokedMethod;
    boolean checkingMethodArgs;
    boolean fieldAccess;
    boolean isNewClass;

    Map<String, PropertyAnnotationType> annotationTypes = new HashMap<>();

    public SMTFilePrinter(BufferedWriter outS, PropertyChecker checker, String varName, String enclClassName, String enclMethodName, String invokedMethod, boolean checkingMethodArgs, boolean fieldAccess, boolean isNewClass) {
        super(outS);
        this.checker = checker;
        this.varName = varName;
        for (BaseTypeChecker typeChecker : this.checker.getSubcheckers()) {
            LatticeAnnotatedTypeFactory lf = (LatticeAnnotatedTypeFactory) typeChecker.getTypeFactory();
            this.annotationTypes.putAll(lf.getLattice().getAnnotationTypes());
        }
        this.enclClassName = enclClassName;
        this.enclMethodName = enclMethodName;
        this.invokedMethod = invokedMethod;
        this.checkingMethodArgs = checkingMethodArgs;
        this.fieldAccess = fieldAccess;
        this.isNewClass = isNewClass;
        print("(set-logic QF_UFNIA)");
        println();

    }

    public void printLine(String line) {
        if (line.contains("assert")) {
            print(line);
            println();
        } else if (line.contains("@")) {
            if (!isNewClass) {
                printProperty(line);
            } else if (checkingMethodArgs) {
                printProperty(line);
            }
        }
    }

    public void printProperty(String prop) {
        String ident = getAnnoIdent(prop);

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

        if (!varName.equals(this.varName.substring(this.varName.indexOf("_") + 1))) {
            for (String sa : smtAnnos) {
                print("(assert " + sa + ")");
                println();
            }
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
            if (!s1.equals("") && !s1.equals(" ")) {
                listAnno.add(s1);
            }
        }
        return listAnno;
    }

    private String toSMT(ArrayList<String> parsedAnno) {
        String smt = "";
        if (parsedAnno.size() == 1) {
            if (isNumeric(parsedAnno.get(0))) {
                smt = parsedAnno.get(0);
            } else {
                String name = findVarName(parsedAnno.get(0));
                //checkDeclarations(name);
                smt = name;
            }
        }
        if (parsedAnno.contains("&&")) {
            smt = parseAnd(parsedAnno, "&&");
        }
        else if (parsedAnno.contains(">=")) {
            smt = parseAnd(parsedAnno, ">=");
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

    private void checkDeclarations(String name) {
        if (!checker.usedVarForVar1.get(varName).contains(name)) {
            print("(declare-const " + name + " Int)");
        }
    }

    private static boolean isNumeric(String str){
        return str != null && str.matches("[0-9.]+");
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
            ///////////////////
            if (isNumeric(parsedAnno.get(0))) {
                lSide = parsedAnno.get(0);
            } else {
                String name = findVarName(parsedAnno.get(0));
                lSide = name;
            }
            ////////////////////////////////
        }
        if (index + 1 < parsedAnno.size() - 1) {
            for (String s : parsedAnno.subList(index + 1, parsedAnno.size())) {
                rightSide.add(s);
            }
            rSide = toSMT(rightSide);
        } else {
            rSide = parsedAnno.get(parsedAnno.size()-1);
            ///////////////////
            if (isNumeric(parsedAnno.get(parsedAnno.size()-1))) {
                rSide = parsedAnno.get(parsedAnno.size()-1);
            } else {
                String name = findVarName(parsedAnno.get(parsedAnno.size()-1));
                rSide = name;
            }
            ////////////////////////////////
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
        print("(assert (or " + smtString + " " + smtCond + "))");
        println();
    }

    private String getSubjectField (String in, String name) {
        String out = "";
        String[] parsedIn = in.split(" ");
        for (int i = 0; i < parsedIn.length; i++) {
            if (parsedIn[i].contains(name)) {
                out = parsedIn[i];
            }
            if (parsedIn[i].contains("§subject§")) {
                out = parsedIn[i].replace("§subject§", name);
            }
        }
        return out;
    }

    private String findVarName(String name) {
        String variable = "notFound";
        if (name.contains("_")) {
            variable = name;
        } else if (fieldAccess) {
            if (checker.usedVarForVar1.containsKey(this.varName)) {
                for (String vn : checker.usedVarForVar1.get(this.varName)) {
                    if (vn.contains(name)) return vn;
                }
            }
        } else
        if (checker.usedVarForVar1.containsKey(this.varName)) {
            for (String s : checker.usedVarForVar1.get(this.varName)) {
                String shortName = s.substring(s.indexOf("_") + 1);
                if (name.equals(shortName)) {
                    variable = s;
                    break;
                }
                if (name.equals(s)) {
                    variable = s;
                    break;
                }
            }
        }
        if (isNumeric(name)) variable = name;
        if (name.equals(this.varName)) variable = this.varName;
        if (variable.equals("notFound")) {
            if (checker.objectFields.containsKey(this.varName + "." + name)) {
                variable = this.varName + "." + name;
            } else {
                for (String v : checker.usedVarForVar1.get(varName)) {
                    if (v.contains(name)) return v;
                }
            }

            //System.out.println("%%%%%%%%%%%" + this.invokedMethod + "_" + name);
            //if (checker.resultsForVar1.containsKey(this.invokedMethod + "_" + name)) {
                //System.out.println("%%%%%%%%%%%" + this.invokedMethod + "_" + name);
            //    variable = this.invokedMethod + "_" + name;
            //}
        }
        return variable;
    }

    private String replaceCondParameters(PropertyAnnotation pa, String name) {
        java.util.List<PropertyAnnotationType.Parameter> parL = pa.getAnnotationType().getParameters();
        java.util.List<String> acPar = pa.getActualParameters();
        String cond = "?";
        if (!parL.isEmpty()) {
            cond = pa.getAnnotationType().getWFCondition();
            for (int i = 0; i < parL.size(); i++) {
                String old = "§" + parL.get(i).getName() + "§";
                String act = "";
                ///////////
                String[] actual = acPar.get(i).split(" ");
                for (int j = 0; j < actual.length; j++) {
                    if (!isNumeric(actual[j]) && !isOperand(actual[j])) {
                        actual[j] = findVarName(actual[j]);
                        //System.out.println("§§§§§§§§" + actual[j]);
                        //checkDeclarations(actual[j]);
                    }
                    act = act + " " + actual[j];
                }
                ///////////////////
                cond = cond.replace(old, act);
            }
            cond = cond.replace("§subject§", varName);
        }
        return cond;
    }

    private static boolean isOperand(String str) {
        if (str.equals("*")) return true;
        if (str.equals("/")) return true;
        if (str.equals("+")) return true;
        if (str.equals("-")) return true;
        if (str.equals("%")) return true;
        return false;
    }

    private String replacePropertyParameters(PropertyAnnotation pa, String name) {
        java.util.List<PropertyAnnotationType.Parameter> parL = pa.getAnnotationType().getParameters();
        java.util.List<String> acPar = pa.getActualParameters();
        String prop = "?";
        if (!parL.isEmpty()) {
            prop = pa.getAnnotationType().getProperty();
            for (int i = 0; i < parL.size(); i++) {
                String old = "§" + parL.get(i).getName() + "§";
                String act = "";
                ///////////
                String[] actual = acPar.get(i).split(" ");
                for (int j = 0; j < actual.length; j++) {
                    if (!isNumeric(actual[j]) && !isOperand(actual[j])) {
                        actual[j] = findVarName(actual[j]);
                        //System.out.println("§§§§§§§§" + actual[j]);
                        //checkDeclarations(actual[j]);
                    }
                    act = act + " " + actual[j];
                }
                ///////////////////
                prop = prop.replace(old, act);
            }
            prop = prop.replace("§subject§", varName);
        }
        return prop;
    }

    private ArrayList<String> getParameterNames(String ident) {
        ArrayList<String> pNames = new ArrayList<String>();
        if (annotationTypes.containsKey(ident)) {
            String typeDef = annotationTypes.get(ident).toString();
            String params = typeDef.substring(typeDef.indexOf("(") + 1, typeDef.indexOf(")"));
            String[] splittedParams = params.split(", ");
            for (String s : splittedParams) {
                String[] typeAndName = s.split(" ");
                if (typeAndName.length > 1) {
                    pNames.add(typeAndName[1]);
                }
            }
        }
        return pNames;
    }

}
