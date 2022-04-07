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

public class AProduct {
    
    public final String title;
    public final @Interval(min="0", max="1000") int price;
    public final @Interval(min="0", max="18") int ageRestriction;
    public final int maxAmount = 10;
    public final int maxSimpleGift = 10;
    public final int bunch = 10;

    @JMLClause("ensures this.title == title && this.price == price && this.ageRestriction == ageRestriction")
    @JMLClause("assignable \\nothing")
    // :: error: inconsistent.constructor.type
    public @AllowedFor(age="ageRestriction") AProduct(
            String title,
            @Interval(min="0", max="1000") int price,
            @Interval(min="0", max="18") int ageRestriction) {
        this.title = title;
        this.price = price;
        this.ageRestriction = ageRestriction;
    }
    
    public @Interval(min = "0", max = "bunch * price") int calculateBunchPrice() {
    	int total = bunch * price;
    	return total;
    }
    
    public @Interval(min = "0", max = "maxSimpleGift") int getGift() {
    	int gift = price / 100;
    	return gift;
    }
    
    public @Interval(min = "0", max = "100") int getBigGift(@Interval(min = "0", max = "maxAmount") int amount) {
    	@Interval(min = "0", max = "maxSimpleGift") int simpleGift = getGift();
    	int bigGift = simpleGift * amount;
    	return bigGift;
    }
}
