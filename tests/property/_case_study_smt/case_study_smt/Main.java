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

public class Main {

	public final int eighteen = 18;
	public final int six = 6;
	public final int fifteen = 15;
    // :: error: inconsistent.constructor.type
    private Main() { }
    
    public void main() {
    
        @AllowedFor(age="eighteen") AProduct product18 = new AProduct("Louisiana Buzzsaw Carnage", 10, eighteen);
        @AllowedFor(age="six") AProduct product6 = new AProduct("Tim & Jeffrey, All Episodes", 10, 6);
        final @Interval(min = "0", max = "product6.price") int price6 = product6.price;
        
        final @Interval(min = "0", max = "price6 * 10") int totalPrice6 = product6.calculateBunchPrice(); 
        
        @AgedOver(age="18") ACustomer customer18 = new ACustomer("Alice", eighteen);
        @AgedOver(age="14") ACustomer customer14 = new ACustomer("Bob", 14);
        @AgedOver(age="fifteen") ACustomer customer15 = new ACustomer("Lisa", fifteen);
        
        addOrder14(customer14, product6);
        addOrder14(customer15, product6);
        final @Interval(min = "1", max = "fifteen + 1") int ordersAmount14 = singleCustomerOrderAmount(0);
        
        addOrder18(customer18, product18);
        addOrder14(customer18, product6);
        final @Interval(min = "1", max = "fifteen + 1") int ordersAmount18 = singleCustomerOrderAmount(1);
        
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
    }
    
    @JMLClauseTranslationOnly("assignable Shop.instance.orders")
    public void addOrder18(@AgedOver(age="18") ACustomer customer, @AllowedFor(age="18") AProduct product) {
        Shop.getInstance().addOrder(Order.order18(customer, product));
    }

    @JMLClauseTranslationOnly("assignable Shop.instance.orders")
    public void addOrder14(@AgedOver(age="14") ACustomer customer, @AllowedFor(age="14") AProduct product) {
        Shop.getInstance().addOrder(Order.order14(customer, product));
    }
    
    public @Interval(min = "1", max = "previousAmount + 1") int singleCustomerOrderAmount(@Interval(min = "0", max = "fifteen") int previousAmount) {
    	int actualAmount = previousAmount + 1;
    	return actualAmount;
    }
}
