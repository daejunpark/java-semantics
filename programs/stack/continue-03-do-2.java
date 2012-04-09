// Testing continue inside do loop, test 2.
// Now continue occurs on first iteration.
// If do statement is desugared to its body followed by a while statement,
// then first continue will be executed outside the loop.
// Such a semantics for do is correct in absence of continue statement,
// but leads to problems when we add semantics for continue.

public class main {

  void main(string[] args) {
    int i=0;
    do {
      int j = i;
      i++;
      if (j % 2 == 0) continue;
      print(j," ");
    } while (i<10);
    print("\n", "Done!", "\n");
  }
}

// 1 3 5 7 9
// Done!
