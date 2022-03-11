package edu.kit.iti.checker.property.printer;

import com.sun.tools.javac.tree.JCTree;
import edu.kit.iti.checker.property.checker.PropertyChecker;

public class SMTStringPrinter {

    String enclClassName;
    String enclMethodName;
    String invokedMethod;
    boolean checkingMethodArgs;
    PropertyChecker checker;

    public SMTStringPrinter(String enclClassName, String enclMethodName, String invokedMethod, boolean checkingMethodArgs, PropertyChecker checker) {
        this.checker = checker;
        this.enclClassName = enclClassName;
        this.enclMethodName = enclMethodName;
        this.invokedMethod = invokedMethod;
        this.checkingMethodArgs = checkingMethodArgs;

    }

    public SMTStringPrinter(PropertyChecker checker) {
        this.checker = checker;
        this.enclClassName = "";
        this.enclMethodName = "";
        this.invokedMethod = "";
        this.checkingMethodArgs = false;
    }

    public String printVarDec(JCTree.JCVariableDecl tree) {
        String smt = "";
        if (tree.init != null) {

            /////////////////
            String variable = tree.name.toString();
            if (!enclMethodName.equals("<init>")) {
                variable = enclClassName + enclMethodName + "_" + variable;
            } else {
                variable = enclClassName + variable;
            }
            if(checkingMethodArgs) {
                variable = enclClassName + invokedMethod + "_" + tree.name.toString();
            }
            ////////////////

            //smt = "(assert (= " + tree.name + " ";// + " " + printExp(tree.init) + "))";
            smt = "(assert (= " + variable + " ";
            if (tree.init.getClass().equals(JCTree.JCBinary.class)) {
                smt = smt + printBinary((JCTree.JCBinary) tree.init);
                //visitBinary((JCTree.JCBinary) tree.init, smt);
            } else {
                smt = smt + printExp(tree.init);
                //printExpr(tree.init);
            }
        }
        return smt + "))";
    }

    public String printVarAssign(JCTree.JCAssign tree) {
        String smt = "";

        /////////////////
        String variable = tree.lhs.toString();
        if (!enclMethodName.equals("<init>")) {
            variable = enclClassName + enclMethodName + "_" + variable;
        } else {
            variable = enclClassName + variable;
        }
        if(checkingMethodArgs) {
            variable = enclClassName + invokedMethod + "_" + tree.lhs.toString();
        }
        ////////////////

        //smt = "(assert (= " + tree.lhs.toString() + " ";
        smt = "(assert (= " + variable + " ";
        if (tree.rhs.getClass().equals(JCTree.JCBinary.class)) {
            smt = smt + printBinary((JCTree.JCBinary) tree.rhs);
            //visitBinary((JCTree.JCBinary) tree.init, smt);
        } else {
            smt = smt + printExp(tree.rhs);
            //printExpr(tree.init);
        }
        return smt + "))";
    }

    public String printExp(JCTree.JCExpression tree) {
        String smt = "";
        if (tree.getKind().toString().equals("INT_LITERAL")) {
            smt = smt + tree.toString();
        } else if(tree.getKind().toString().equals("IDENTIFIER")) {
            String name = enclClassName + enclMethodName + "_" + tree.toString();
            if (checker.resultsForVar1.containsKey(name)) {
                smt = smt + name;
            } else {
                name = enclClassName + "_" + tree.toString();
                smt = smt + name;
            }
        } else {
            smt = smt + tree.toString();
        }
        return smt;
    }

    public String printBinary(JCTree.JCBinary tree) {
        String smt = "";
        smt = "(" + printTag(tree.getTag()) + " ";// + " " + printExp(tree.lhs) + " " + printExp(tree.rhs);
        if (tree.lhs.getClass().equals(JCTree.JCBinary.class)) {
            smt = smt + printBinary((JCTree.JCBinary) tree.lhs);
        } else if (tree.lhs.getClass().equals(JCTree.JCParens.class)) {
            smt = smt + printParens((JCTree.JCParens) tree.lhs);
        } else {
            smt = smt + printExp(tree.lhs);
        }
        smt = smt + " ";
        if (tree.rhs.getClass().equals(JCTree.JCBinary.class)) {
            smt = smt + printBinary((JCTree.JCBinary) tree.rhs);
        } else if (tree.rhs.getClass().equals(JCTree.JCParens.class)) {
            smt = smt + printParens((JCTree.JCParens) tree.rhs);
        } else {
            smt = smt + printExp(tree.rhs);
        }
        smt = smt + ")";
        return smt;
    }

    public String printParens(JCTree.JCParens tree) {
        String smt = "";
        if (tree.getExpression().getClass().equals(JCTree.JCBinary.class)) {
            smt = smt + printBinary((JCTree.JCBinary) tree.getExpression());
        } else {
            smt = smt + printExp(tree.getExpression());
        }
        return smt;
    }

    public String printTag(JCTree.Tag tag) {
        String smt = "";
        switch (tag) {
            case MINUS: smt = "-";
            break;
            case PLUS: smt = "+";
            break;
            case MUL: smt = "*";
            break;
            case DIV: smt = "div";
            break;
            case MOD: smt = "mod";
            break;
            default: break;
        }
        return smt;
    }

}
