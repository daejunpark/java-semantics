// Testing continue with label inside simple for loop

public class main {

  void main(string[] args) {
    label_1:
    for(int i=0; i<10; i++) {
      if (i % 2 != 0) continue label_1;
      print(i," ");
    }
    print("\n", "Done!", "\n");
  }
}

// 0 2 4 6 8
// Done!
