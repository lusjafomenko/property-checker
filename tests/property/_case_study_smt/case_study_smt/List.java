/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package case_study_smt; 

import edu.kit.iti.checker.property.subchecker.lattice.case_study_smt_qual.*;
import edu.kit.iti.checker.property.checker.qual.*;

public class List {
    
    private final Object head;
    
    private final @Nullable
    @Length(min="this.size - 1", max="this.size - 1")
    List tail;
    
    public final @Positive int size;

    @JMLClause("assignable \\nothing")
    public
    @Length(min="tail.size + 1", max="tail.size + 1")
    // :: error: inconsistent.constructor.type
    List(Object head, List tail) {
        // :: error: assignment.type.incompatible
        this.size = tail.size() + 1;
        this.head = head;
        // :: error: assignment.type.incompatible
        this.tail = tail;
    }

    @JMLClause("assignable \\nothing")
    public
    @Length(min="1", max="1")
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
    @Length(min="this.size - 1", max="this.size - 1")
    List tail() {
        // :: error: return.type.incompatible
        return tail;
    }

    @JMLClause("ensures \result == this.size")
    @JMLClause("assignable \\nothing")
    public @Positive int size() {
        return size;
    }

    @JMLClause("ensures l != null ==> \result == l.size")
    @JMLClause("ensures l == null ==> \result == 0")
    @JMLClause("assignable \\nothing")
    public static @NonNegative int size(@Nullable List l) {
        if (l == null) {
            return 0;
        } else {
            // :: error: method.invocation.invalid
            return l.size();
        }
    }
}
