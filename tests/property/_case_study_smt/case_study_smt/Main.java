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

	public static final int eighteen = 18;
	public static final int six = 6;
	public static final int fifteen = 15;
    // :: error: inconsistent.constructor.type
    private Main() { }
    
    public static void main(String[] args) {
    
        @AllowedFor(age="eighteen") AProduct product18 = new AProduct("Louisiana Buzzsaw Carnage", 10, eighteen);
        @AllowedFor(age="six") AProduct product6 = new AProduct("Tim & Jeffrey, All Episodes", 10, 6);
        @Interval(min = "0", max = "product6.price") int price6 = product6.price;
        
        ///////// !!!
        @Interval(min = "0", max = "price6 * 10") int totalPrice6 = product6.calculateBulkPrice(); 
        
        @AgedOver(age="18") Customer customer18 = new Customer("Alice", eighteen);
        @AgedOver(age="14") Customer customer14 = new Customer("Bob", 14);
        @AgedOver(age="fifteen") Customer customer15 = new Customer("Lisa", fifteen);
        
        addOrder14(customer14, product6);
        addOrder14(customer15, product6);
        @Interval(min = "1", max = "fifteen + 1") int ordersAmount14 = singleCustomerOrderAmount(0);
        
        addOrder18(customer18, product18);
        addOrder14(customer18, product6);
        @Interval(min = "1", max = "fifteen + 1") int ordersAmount18 = singleCustomerOrderAmount(1);
        
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
    }
    
    @JMLClauseTranslationOnly("assignable Shop.instance.orders")
    public static void addOrder18(@AgedOver(age="18") Customer customer, @AllowedFor(age="18") AProduct product) {
        Shop.getInstance().addOrder(Order.order18(customer, product));
    }

    @JMLClauseTranslationOnly("assignable Shop.instance.orders")
    public static void addOrder14(@AgedOver(age="14") Customer customer, @AllowedFor(age="14") AProduct product) {
        Shop.getInstance().addOrder(Order.order14(customer, product));
    }
    
    public static @Interval(min = "1", max = "previousAmount + 1") int singleCustomerOrderAmount(@Interval(min = "0", max = "fifteen") int previousAmount) {
    	int actualAmount = previousAmount + 1;
    	return actualAmount;
    }
}
