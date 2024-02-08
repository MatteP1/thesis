#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <stdlib.h>

typedef struct Pointer Pointer;
typedef struct Node Node;
typedef struct Queue Queue;

struct Pointer {Node* ptr; int count;};
struct Node {int value; Pointer next;};
struct Queue {Pointer Head; Pointer Tail;};

void printPointer(Pointer p){
    printf("Pointer\n");
    printf("Node*: %p\n", p.ptr);
    printf("Count: %d\n", p.count);
}

void printNode (Node n){
    printf("Node\n");
    printf("Value: %d\n", n.value);
    printPointer(n.next);
}

void printQueue (Queue q){
    printf("Queue\n");
    printf("Head ");
    printPointer(q.Head);
    printf("Tail" );
    printPointer(q.Tail);
}

int pointerCompare (Pointer p1, Pointer p2) {
    if (p1.count == p2.count && p1.ptr == p2.ptr){
        return 1;
    } else {
        return 0;
    }
}

Node* new_node() {
    Node* newnode = (Node*)malloc(sizeof(Node));
    Pointer newpointer = {.ptr=NULL, .count=0};
    newnode->value = 0;
    newnode->next=newpointer;
    return newnode;
}


void initialize(Queue *Q){
    Node* newnode = new_node();
    Q->Head.ptr = newnode;
    Q->Tail.ptr = newnode;
}

void enqueue(Queue *Q, int value){
    Node* node = new_node();
    node->value = value;
    node->next.ptr = NULL;
    Pointer tail;
    while (1) {
        Pointer tail = Q->Tail;
        Pointer next = tail.ptr->next;
        printf("TAIL AND NEXT\n");
        printPointer(tail);
        printPointer(next);
        if (next.ptr == NULL) {
            Pointer np = {.ptr=node, .count = next.count + 1};
            int test = atomic_compare_exchange_strong(&(tail.ptr->next), &next, np);
            if (test){
                break;
            }
        } else {
            Pointer np = {.ptr=next.ptr, .count = tail.count + 1};
            atomic_compare_exchange_strong(&(Q->Tail), &tail, np);
        }
    }
    Pointer np = {.ptr=node, .count = tail.count + 1};
    atomic_compare_exchange_strong(&(Q->Tail), &tail, np);
}

int dequeue(Queue *Q, int *pvalue){
    Pointer head;
    while (1) {
        Pointer head = Q->Head;
        Pointer tail = Q->Tail;
        Pointer next = head.ptr->next;
        if (pointerCompare(head, Q->Head)) {
            if (head.ptr == tail.ptr) {
                if (next.ptr == NULL) {
                    return 0;
                }
                Pointer np = {.ptr=next.ptr, .count = tail.count + 1};
                atomic_compare_exchange_strong(&(Q->Tail), &tail, np);
            } else {
                *pvalue = next.ptr->value;
                Pointer np = {.ptr=next.ptr, .count = head.count + 1};
                int test = 
                    atomic_compare_exchange_strong(&(Q->Head), &head, np);
                if (test) {
                    break;
                }
            }
        }
    }
    free(head.ptr);
    return 1;
}


int main() {
    Queue* q = &((Queue) {.Head = NULL, .Tail = NULL});
    initialize(q);
    printQueue(*q);
    enqueue(q, 4);
    int* r = NULL;
    dequeue(q, r);
    printf("test: %d", *r);
}