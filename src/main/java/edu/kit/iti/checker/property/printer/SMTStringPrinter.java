package edu.kit.iti.checker.property.printer;

import com.sun.tools.javac.tree.JCTree;

public class SMTStringPrinter {


    public SMTStringPrinter() {

    }

    public String printVarDec(JCTree.JCVariableDecl tree) {
        String smt = "";
        if (tree.init != null) {
            smt = "(assert (= " + tree.name + " ";// + " " + printExp(tree.init) + "))";
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

    public String printExp(JCTree.JCExpression tree) {
        String smt = "";
        return smt + tree.toString();
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
