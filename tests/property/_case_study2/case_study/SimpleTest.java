package case_study;

import edu.kit.iti.checker.property.subchecker.lattice.case_study_qual.*;
import edu.kit.iti.checker.property.checker.qual.*;

public class SimpleTest {

	
	public int t;
	public int v = 1;
	public int z = 2 + 1 + 7 + 6;
	public int w = 2 * 2 + 1;
	public int c = 1 + 2 * 2;
	public int r = 1 + 2 * 3 / 4 - 5 * 6 + 7 / 8 / 9;
	public final int x = 0 / 5;
	public @Interval(min="14", max="150") int a = 15 + 1;
	
	public final int y = x * 2;
	
	public static @Interval(min = "1", max = "var+1") int addOne(@Interval(min = "0", max = "var5")int var, int var5, String var6) {
		@Interval(min = "0", max = "r") int m = var + 1;
		return m;
	} 
	
	public @Interval(min = "0", max = "z") int dummy() {
		@Interval(min = "0", max = "z") int m1;
		return m1 = 0;
	}
	
	
	
}
