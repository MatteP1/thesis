import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;
import java.util.random.*;
import java.util.stream.Stream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

class Node {
    int value;
    AtomicReference<Node> next;

	Node() {
		this.value = 0;
		this.next = new AtomicReference<Node>(null);
	}
	Node(int value) {
        this.value = value;
        this.next = new AtomicReference<Node>(null);
    }

    Node(int value, AtomicReference<Node> next) {
        this.value = value;
        this.next = next;
    }
}

// Pointer class not needed s AtomicReference compares using == (i.e. object references)

class Queue {
    AtomicReference<Node> Head;
    AtomicReference<Node> Tail;

    Queue() {
        Node newnode = new Node();

		this.Head = new AtomicReference<Node>(newnode);
		this.Tail = new AtomicReference<Node>(newnode);
    }

    void enqueue(int value) {
        Node node = new Node(value);
		Node tail;
        while (true) {
        	tail = Tail.get();
            Node next = tail.next.get();
			if (tail != Tail.get()) continue;
            if (next == null) {
                if (tail.next.compareAndSet(next, node)) {
                    break;
                }
            } else {
                Tail.compareAndSet(tail, next);
            }
        }
        Tail.compareAndSet(tail, node);
    }

    boolean dequeue(AtomicReference<Integer> pvalue) {
		Node head;
        while (true) {
            head = Head.get();
            Node tail = Tail.get();
            Node next = head.next.get();
            if (head == Head.get()) {
                if (head == tail) {
                    if (next == null) {
                        return false;
                    }
                    Tail.compareAndSet(tail, next);
                } else {
                    pvalue.set(next.value);
                    if (Head.compareAndSet(head, next)) {
                        break;
                    }
                }
            }
        }
        head = null;
        return true;
    }

	@Override
	public String toString(){
		Node node = Head.get();
		StringBuilder stringBuilder = new StringBuilder();
		while (true){
			if (node != null) {
				stringBuilder.append("Node: " + node.value + "\n");
				node = node.next.get();
			} else {
				break;
			}
		}
		return stringBuilder.toString();
	}
}


// TESTING
class Producer implements Runnable {
	
	private Queue q;
    private Iterator<Integer> elems;

	Producer(Queue q, List<Integer> elements){
		this.q = q;
        this.elems = elements.iterator();
	}

	public void run() {
        while (elems.hasNext()) {
            int value = elems.next();
		    q.enqueue(value);
        }
	}
}

class Consumer implements Runnable {
	private Queue q;
    private AtomicInteger counter;
    private AtomicInteger adds;
    private int total;

	Consumer(Queue q, AtomicInteger counter, AtomicInteger adds, int total){
		this.q = q;
        this.counter = counter;
        this.adds = adds;
        this.total = total;
	}

	public void run() {
        while (adds.get() < total) {
            AtomicReference<Integer> result = new AtomicReference<>(null);
            boolean success = q.dequeue(result);
            if (success) {
                counter.addAndGet(result.get());
                adds.incrementAndGet();
            }
        }
	}
}


public class msqueue {
    public static void main(String[] args) throws InterruptedException {
        Queue q = new Queue();
        AtomicInteger counter = new AtomicInteger(0);
        AtomicInteger adds = new AtomicInteger(0);

        int numberOfConsumers = 3;
        int numberOfProducers = 4;
        int workload_size = 3000;
        Random random = new Random();

        List<Integer> list = new ArrayList<Integer>();
        // Create producers
        List<Producer> producers = new ArrayList<>();
        for (int p = 0; p < numberOfProducers; p++){
            List<Integer> workload = new ArrayList<>();
            for (int i = 0; i < workload_size; i++) {
                int n = random.nextInt(4000);
                workload.add(n);
                list.add(n);
            }
            Producer producer = new Producer(q, workload);
            producers.add(producer);
        }

        // Create consumers
        List<Consumer> consumers = new ArrayList<>();
        for (int c = 0; c < numberOfConsumers; c++){
            consumers.add(new Consumer(q, counter, adds, workload_size * numberOfProducers));
        }

        List<Thread> producerThreads = producers.stream()
                                                .map(p -> new Thread(p))
                                                .toList();
        List<Thread> consumerThreads = consumers.stream()
                                                .map(p -> new Thread(p))
                                                .toList();
        for (Thread t : producerThreads){
            t.start();
        }
        for (Thread t : consumerThreads){
            t.start();
        }

        int answer = list.stream().reduce(0, (a, b) -> a + b);
        System.out.println("Answer: " + answer);
        for (Thread t : producerThreads){
            t.join();
        }
        for (Thread t : consumerThreads){
            t.join();
        }
        System.out.println(adds.get());
        System.out.println(workload_size * numberOfProducers);
        System.out.println("Counter: " + counter);
    }
}