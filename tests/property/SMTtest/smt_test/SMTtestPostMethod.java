package smt_test;

import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public class SMTtestPostMethod {
	
	@Less(value="10") int vp = 5;
	int tttp = 10;
	int twwwo = 2;
	int onne = 1;
	
	
	public void testPostMethod() {
		SMTtestMethod mp = new SMTtestMethod();
		//int twenty = m.age;
		@Interval(min = "0", max = "tttp") int tenp = mp.x;
		
		SMTtestMethod ma = new SMTtestMethod(10);
		SMTtestMethod mb = new SMTtestMethod(180);
		@Length1(min = "onne", max = "onne") List li1 = new List("DEF");
		//@Length1(min = "twwwo", max = "twwwo") List li0 = new List(String "ABC", li1);
	}
}
