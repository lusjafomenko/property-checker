package smt_test;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;
import edu.kit.iti.checker.property.checker.qual.*;


public class List {
    
    private final Object head;
    
    private final @Nullable
    @Length1(min = "this.size - 1", max = "this.size - 1")
    List tail;
    
    public final @Interval(min = "1", max = "1000") int size;

    @JMLClause("assignable \\nothing")
    public
    @Length1(min = "tail.size + 1", max = "tail.size + 1")
    // :: error: inconsistent.constructor.type
    List(Object head, List tail) {
        // :: error: assignment.type.incompatible
        this.size = tail.size + 1;
        this.head = head;
        // :: error: assignment.type.incompatible
        this.tail = tail;
    }

    @JMLClause("assignable \\nothing")
    public
    @Length1(min = "1", max = "1")
    // :: error: inconsistent.constructor.type
    List(Object head) {
        this.size = 1;
        this.head = head;
        // :: error: assignment.type.incompatible
        this.tail = null;
    }

    @JMLClause("assignable \\nothing")
    public static List cons(Object head, @Nullable List tail) {
        if (tail != null) {
            // :: error: argument.type.incompatible
            return new List(head, tail);
        } else {
            return new List(head);
        }
    }

    @JMLClause("assignable \\nothing")
    public Object head() {
        return head;
    }

    @JMLClause("assignable \\nothing")
    public
    @Nullable
    @Length1(min = "this.size - 1", max = "this.size - 1")
    List tail() {
        // :: error: return.type.incompatible
        return tail;
    }

    //@JMLClause("ensures \result == this.size")
    //@JMLClause("assignable \\nothing")
    //public @Interval(min = "1", max = "1000") int size() {
    //    return size;
    //}

    @JMLClause("ensures l != null ==> \result == l.size")
    @JMLClause("ensures l == null ==> \result == 0")
    @JMLClause("assignable \\nothing")
    public static @Interval(min = "0", max = "1000") int size(@Nullable List l) {
        if (l == null) {
            return 0;
        } else {
            // :: error: method.invocation.invalid
            return l.size;
        }
    }
}
