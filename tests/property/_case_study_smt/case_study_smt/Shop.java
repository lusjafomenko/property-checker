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

public class Shop {
    
    public static Shop instance = new Shop();

    @JMLClauseTranslationOnly("ensures \result == instance")
    @JMLClauseTranslationOnly("assignable \\nothing")
    public static Shop getInstance() {
        return instance;
    }
    
    private @Okasaki Queue orders = Queue.empty();

    // :: error: inconsistent.constructor.type
    private Shop() { }

    @JMLClauseTranslationOnly("assignable orders")
    public void addOrder(Order order) {
        orders = orders.insert(order).toOkasaki();
    }

    public boolean processNextOrder() {
        if (orders.size() > 0) {
            orders = orders.removeIfPresent().toOkasaki();
            return true;
        } else {
            return false;
        }
    }
}
