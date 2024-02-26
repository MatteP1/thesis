#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>
#include <stdlib.h>

typedef struct Node Node;
typedef struct Queue Queue;

struct Node {int value; Node** next;};
struct Queue {Node** Head; Node** Tail;};

void printNode (Node* n){
    printf("Node\n");
    printf("Value: %d\n", n->value);
}

void printQueue (Queue* Q){
    printf("Queue\n");
    printf("Head ");
    printNode(*(Q->Head));
    printf("Tail " );
    printNode(*(Q->Tail));
}

Node* new_node() {
    Node* newnode = (Node*)malloc(sizeof(Node));
    newnode->value = 0;
    newnode->next = malloc(sizeof(void*));
    *(newnode->next) = NULL;
    return newnode;
}


void initialize(Queue* Q){
    Node* newnode = new_node();
    Q->Head = malloc(sizeof(void*));
    *(Q->Head) = newnode;
    Q->Tail = malloc(sizeof(void*));
    *(Q->Tail) = newnode;
}

void enqueue(Queue *Q, int value){
    Node* node = new_node();
    node->value = value;
    Node** tail;
    while (1) {
        tail = Q->Tail;
        Node** next = (*tail)->next;
        if (*next == NULL) {
            // printNode(*next);
            // printNode(node);
            int test = atomic_compare_exchange_strong((*tail)->next,
                                                      next,
                                                      node);
            if (test){
                break;
            }
        } else {
            atomic_compare_exchange_strong(Q->Tail, tail, *next);
        }
    }
    atomic_compare_exchange_strong(Q->Tail, tail, node);
}

int dequeue(Queue *Q, int *pvalue){
    Node* head;
    while (1) {
        Node** head = Q->Head;
        Node** tail = Q->Tail;
        Node** next = (*head)->next;
        if (*head == *(Q->Head)) {
            if (*head == *tail) {
                if (*next == NULL) {
                    return 0;
                }
                atomic_compare_exchange_strong(Q->Tail, tail, *next);
            } else {
                *pvalue = (*next)->value;
                int test = 
                    atomic_compare_exchange_strong(Q->Head, head, *next);
                if (test) {
                    break;
                }
            }
        }
    }
    // Avoid freeing as M&S Queue is unsafe when freeing:
    // It can happen that one thread frees head, and another tries to read 
    // just before another tries to do head->next
    // free(head);
    return 1;
}


int main() {
    Queue* Q = &((Queue) {.Head = NULL, .Tail = NULL});
    initialize(Q);
    printQueue(Q);
    enqueue(Q, 4);
    int* r = malloc(sizeof(int));
    printQueue(Q);
    dequeue(Q, r);
    printf("test: %d\n", *r);
}