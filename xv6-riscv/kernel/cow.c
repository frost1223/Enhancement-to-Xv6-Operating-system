#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "elf.h"
#include <stdbool.h>

struct spinlock cow_lock;

// Max number of pages a CoW group of processes can share
#define SHMEM_MAX 100

struct cow_group {
    int group; // group id
    uint64 shmem[SHMEM_MAX]; // list of pages a CoW group share
    int count; // Number of active processes
};

struct cow_group cow_group[NPROC];

struct cow_group* get_cow_group(int group) {
    if(group == -1)
        return 0;

    for(int i = 0; i < NPROC; i++) {
        if(cow_group[i].group == group)
            return &cow_group[i];
    }
    return 0;
}

void cow_group_init(int groupno) {
    for(int i = 0; i < NPROC; i++) {
        if(cow_group[i].group == -1) {
            cow_group[i].group = groupno;
            return;
        }
    }
} 

int get_cow_group_count(int group) {
    return get_cow_group(group)->count;
}
void incr_cow_group_count(int group) {
    get_cow_group(group)->count = get_cow_group_count(group)+1;
}
void decr_cow_group_count(int group) {
    get_cow_group(group)->count = get_cow_group_count(group)-1;
}

void add_shmem(int group, uint64 pa) {
    if(group == -1)
        return;

    uint64 *shmem = get_cow_group(group)->shmem;
    int index;
    for(index = 0; index < SHMEM_MAX; index++) {
        // duplicate address
        if(shmem[index] == pa)
            return;
        if(shmem[index] == 0)
            break;
    }
    shmem[index] = pa;
}

int is_shmem(int group, uint64 pa) {
    if(group == -1)
        return 0;

    uint64 *shmem = get_cow_group(group)->shmem;
    for(int i = 0; i < SHMEM_MAX; i++) {
        if(shmem[i] == 0)
            return 0;
        if(shmem[i] == pa)
            return 1;
    }
    return 0;
}

void cow_init() {
    for(int i = 0; i < NPROC; i++) {
        cow_group[i].count = 0;
        cow_group[i].group = -1;
        for(int j = 0; j < SHMEM_MAX; j++)
            cow_group[i].shmem[j] = 0;
    }
    initlock(&cow_lock, "cow_lock");
}

int uvmcopy_cow(pagetable_t old, pagetable_t new, uint64 sz, int group) {
    
    /* CSE 536: (2.6.1) Handling Copy-on-write fork() */

    // Copy user vitual memory from old(parent) to new(child) process

    // Map pages as Read-Only in both the processes
    pte_t *pte;
    uint64 pa, i;
    uint flags;
    // char *mem;

    for(i = 0; i < sz; i += PGSIZE){
        if((pte = walk(old, i, 0)) == 0)
        panic("uvmcopy_cow: pte should exist");
        if((*pte & PTE_V) == 0)
        panic("uvmcopy: page not present");
        *pte &= ~PTE_W;
        pa = PTE2PA(*pte);
        
        flags = PTE_FLAGS(*pte);
        // if((mem = kalloc()) == 0)
        // goto err;
        // memmove(mem, (char*)pa, PGSIZE);
        if(mappages(new, i, PGSIZE, pa, flags) != 0){
        // kfree(mem);
            panic("Luchu pattak: page not present");
        }
        add_shmem(group, pa);
    }
  return 0;
    // return 0;
}

void copy_on_write(struct proc* p, uint64 faulting_addr) {

    pte_t *pte;
    uint64 pa;
    uint flags;
    /* CSE 536: (2.6.2) Handling Copy-on-write */
    // uint64 round_fault = PGROUNDDOWN(faulting_addr);

    print_copy_on_write(p, faulting_addr);

    // Allocate a new page 
    char *mem = kalloc();
    pte = walk(p->pagetable, faulting_addr, 0);
    
    pa = PTE2PA(*pte);
    flags = PTE_FLAGS(*pte);
    flags |= PTE_W;
    // Copy contents from the shared page to the new page
    memmove(mem, (char*)pa, PGSIZE);
    uvmunmap(p->pagetable, faulting_addr, 1, 0);

    // Map the new page in the faulting process's page table with write permissions
    mappages(p->pagetable, faulting_addr, PGSIZE, pa, flags);
    
}
