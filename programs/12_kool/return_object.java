// Test returning objects in methods and then invoking methods on them

class I {
  int val;
  I(int v) {
    val = v;
  }
  G m1() {
    return (new G(val + 9));
  }
}

class G {
  int a;
  G(int t) {
    a = t;
  }
  void print2() { System.out.println(a); }
}

class main {
  main(String[] args) {
    ((new I(1)).m1()).print2();
    System.out.println("Done!");
  }
}

public class return_object {
  public static void main(String[] args) {
    new main(args);
  }
}

// 10
// Done!
