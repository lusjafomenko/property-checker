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

public class Queue {
    
    public final @Nullable List front;
    public final @Nullable List back;

    @JMLClause("ensures \result.front == null && \result.back == null")
    @JMLClause("assignable \\nothing")
    public static @Okasaki Queue empty() {
        // :: error: return.type.incompatible
        return new Queue(null, null);
    }

    @JMLClause("ensures this.front == front && this.back == back")
    @JMLClause("assignable \\nothing")
    // :: error: inconsistent.constructor.type
    public Queue(@Nullable List front, @Nullable List back) {
        this.front = front;
        this.back = back;
    }

    @JMLClause("ensures front != null || back != null || acc != null ==> \result != null")
    @JMLClause("assignable \\nothing")
    private static @Nullable List rotate(@Nullable List front, @Nullable List back, @Nullable List acc) {
        if (front == null && back == null) {
            return acc;
        } else if (front == null) {
            // :: error: method.invocation.invalid
            return rotate(null, back.tail(), List.cons(back.head(), acc));
        } else if (back == null) {
            return List.cons(
                    // :: error: method.invocation.invalid
                    front.head(),
                    // :: error: method.invocation.invalid
                    rotate(front.tail(), null, acc));
        } else {
            return List.cons(
                    // :: error: method.invocation.invalid
                    front.head(),
                    // :: error: method.invocation.invalid
                    rotate(front.tail(), back.tail(), List.cons(back.head(), acc)));
        }
    }


    @JMLClause("ensures this.front != null || this.back != null ==> \result.front != null")
    @JMLClause("assignable \\nothing")
    public @Okasaki Queue toOkasaki() {
        // :: error: method.invocation.invalid
        if (back == null || (front != null && front.size() >= back.size())) {
            // :: error: return.type.incompatible
            return this;
        } else {
            Queue res = new Queue(rotate(front, back, null), null);
            // :: error: return.type.incompatible
            return res;
        }
    }

    @JMLClause("ensures front == null && back == null ==> \result == 0")
    @JMLClause("ensures front == null && back != null ==> \result == back.size")
    @JMLClause("ensures front != null && back == null ==> \result == front.size")
    @JMLClause("ensures front != null && back != null ==> \result == front.size + back.size")
    @JMLClause("assignable \\nothing")
    public int size() {
        return List.size(front) + List.size(back);
    }

    @JMLClause("assignable \\nothing")
    public Object peek(@FrontNonEmpty Queue this) {
        // :: error: method.invocation.invalid
        return front.head();
    }

    @JMLClause("assignable \\nothing")
    public Queue remove(@FrontNonEmpty Queue this) {
        // :: error: method.invocation.invalid
        return new Queue(front.tail(), back);
    }

    @JMLClause("assignable \\nothing")
    public Queue removeIfPresent() {
        if (size() > 0) {
            if (front != null) {
                // :: error: method.invocation.invalid
                return remove();
            } else {
                // :: error: method.invocation.invalid
                return toOkasaki().remove();
            }
        } else {
            return this;
        }
    }

    @JMLClause("assignable \\nothing")
    public Queue insert(Object o) {
        return new Queue(front, List.cons(o, back));
    }
}
