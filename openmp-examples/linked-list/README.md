# Linked-List Example Application

This is a simple example application which demonstrates the capabilites of the HERO's shared virtual memory (SVM) system.
A graph stored as a linked list or adjacency list is allocated in regular, virtual memory on the host using standard `malloc()` and shared with the accelerator.
Thanks to SVM, the accelerator can then access the graph and follow internal references using the same virtual address pointers as the host.
