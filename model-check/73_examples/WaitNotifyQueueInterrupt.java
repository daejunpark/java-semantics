/*
  Same as WaitNotifyQueue, but the consumer thread is itnerrupted at the end of main().
  10 solutions expected:
  - 4 non-interruption solutions:
      put put get put get get
      put put get get put get
      put get put put get get
      put get put get put get
  + 6 solutions when consumer is interrupted:
    - 1 solution for each case with 1 get at the end
    - 2 solutions for each case with 1 get at the end
*/
public class WaitNotifyQueueInterrupt {
  public static void main(String[] args) throws Exception {
    final BlockingQueue queue = new BlockingQueue();
    Thread t2 = new Thread() {
      public void run() {
        for(int i=0; i<3; i++) {
          try {
            queue.get();
          } catch(InterruptedException e) {
            System.out.println("Interrupted.");
            return;
          }
        }
      }
    };
    t2.start();
    for(int i=0; i<3; i++) {
      queue.put(i);
    }
    t2.interrupt();
  }

  static class BlockingQueue {
    int[] array = new int[2];
    int size=0;
    synchronized void put(int element) throws InterruptedException {
      while(size == array.length) {
        wait();
      }
      array[size++]=element;
      System.out.print("put-" + element + " ");
      notify();
    }
    synchronized int get() throws InterruptedException {
      while(size == 0) {
        wait();
      }
      int element = array[--size];
      System.out.print("get-" + element + " ");
      notify();
      return element;
    }
  }
}