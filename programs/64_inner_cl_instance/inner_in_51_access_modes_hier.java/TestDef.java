/*
    - TestDef.Inner5   < p1.A
    - TestDef.Inner6   < p1.B.InnerB
*/

public class TestDef extends p1.B {

  public class Inner5 extends p1.A {
    public String test() {
      return "p1.TestP1.Inner5.test():    " + f((byte)0);
    }
  }

  public class Inner6 extends p1.B.InnerB {
    public String test() {
      return "p1.TestP1.Inner6.test():    " + f((byte)0);
    }
  }
}
