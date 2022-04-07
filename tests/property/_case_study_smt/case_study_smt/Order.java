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

public class Order {
    
    public final int witness;
    public final @AgedOver(age="witness") ACustomer customer;
    public final @AllowedFor(age="witness") AProduct product;

    @JMLClause("ensures this.customer == customer && this.product == product && this.witness == witness")
    @JMLClause("assignable \\nothing")
    // :: error: inconsistent.constructor.type
    public Order(int witness, @AgedOver(age="witness") ACustomer customer, @AllowedFor(age="witness") AProduct product) {
        this.witness = witness;
        // :: error: assignment.type.incompatible
        this.customer = customer;
        // :: error: assignment.type.incompatible
        this.product = product;
    }

    @JMLClause("ensures \result.customer == customer && \result.product == product && \result.witness == 18")
    @JMLClause("assignable \\nothing")
    public static Order order18(@AgedOver(age="18") ACustomer customer, @AllowedFor(age="18") AProduct product) {
        // :: error: argument.type.incompatible
        return new Order(18, customer, product);
    }

    @JMLClause("ensures \result.customer == customer && \result.product == product && \result.witness == 14")
    @JMLClause("assignable \\nothing")
    public static Order order14(@AgedOver(age="14") ACustomer customer, @AllowedFor(age="14") AProduct product) {
        // :: error: argument.type.incompatible
        return new Order(14, customer, product);
    }
}
