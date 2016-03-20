public class treap {
    int value;
    int priority;
    treap left;
    treap right;

    treap (int value, int priority)
    {
        this.value = value;
        this.priority = priority;
        this.left = null;
        this.right = null;
    }

    public static void main(String[] args) {
        treap t = null;
        t = insert(1,10,t);
        t = insert(2,30,t);
        t = insert(3,20,t);
        t = delete(2,t);
    }

    static treap left_rotate(treap x)
    {
        treap y = x.right;
        x.right = y.left;
        y.left = x;
        return y;
    }

    static treap right_rotate(treap x)
    {
        treap y = x.left;
        x.left = y.right;
        y.right = x;
        return y;
    }

// Find

    static boolean find(int v, treap t)
    {
        if (t == null)
            return false;
        else if (v == t.value)
            return true;
        else if (v < t.value)
            return find(v, t.left);
        else
            return find(v, t.right);
    }


// Insert

    static treap insert(int v, int p, treap t)
    {
      if (t == null) {
        return new treap(v, p);
      }
      if (v < t.value) {
        t.left = insert(v, p, t.left);
        if (t.left.priority > t.priority) {
          t = right_rotate(t);
        }
      } else if (v > t.value) {
        t.right = insert(v, p, t.right);
        if (t.right.priority > t.priority) {
          t = left_rotate(t);
        }
      }
      return t;
    }

// Remove

    static treap delete_root(treap t) {
      if (t.left == null) {
        t = t.right;
      } else if (t.right == null) {
        t = t.left;
      } else {
        if (t.left.priority < t.right.priority) {
          t = left_rotate(t);
          t.left = delete_root(t.left);
        } else {
          t = right_rotate(t);
          t.right = delete_root(t.right);
        }
      }
      return t;
    }

    static treap delete(int v, treap t) {
      if (t == null) {
        return null;
      }
      if (v == t.value) {
        t = delete_root(t);
      } else if (v < t.value) {
        t.left = delete(v, t.left);
      } else {
        t.right = delete(v, t.right);
      }
      return t;
    }
}
