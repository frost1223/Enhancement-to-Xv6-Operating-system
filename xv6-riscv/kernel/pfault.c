/* This file contains code for a generic page fault handler for processes. */
#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "elf.h"

#include "sleeplock.h"
#include "fs.h"
#include "buf.h"

int loadseg(pagetable_t pagetable, uint64 va, struct inode *ip, uint offset, uint sz);
int flags2perm(int flags);

/* CSE 536: (2.4) read current time. */
uint64 read_current_timestamp() {
  uint64 curticks = 0;
  acquire(&tickslock);
  curticks = ticks;
  wakeup(&ticks);
  release(&tickslock);
  return curticks;
}

bool psa_tracker[PSASIZE];

/* All blocks are free during initialization. */
void init_psa_regions(void)
{
    for (int i = 0; i < PSASIZE; i++) 
        psa_tracker[i] = false;
}

/* Evict heap page to disk when resident pages exceed limit */
void evict_page_to_disk(struct proc* p) {

    /* Find free block */
    int blockno = 0;
    for(int i = 0; i < PSASIZE; i++){
        if(psa_tracker[i] == false){
            blockno = psa_tracker[i];
            break;
        }
    }

    /* Find victim page using FIFO. */
    uint64 victim_page_time = p->heap_tracker[0].last_load_time;
    // uint64 victim_page = 0;
    int block_tacker = 0;
    for(int i = 0; i<MAXHEAP; i++){
        if(p->heap_tracker[i].last_load_time < victim_page_time){
            victim_page_time = p->heap_tracker[i].last_load_time;
            block_tacker = i;
        }
        
    }
    uint64 victim_page = p->heap_tracker[block_tacker].addr;
    

    char *kernel_page = kalloc();
    copyin(p->pagetable, kernel_page, victim_page, PGSIZE);
    
    /* Print statement. */
    print_evict_page(victim_page, blockno);
    /* Read memory from the user to kernel memory first. */
    
    /* Write to the disk blocks. Below is a template as to how this works. There is
     * definitely a better way but this works for now. :p */

    struct buf* b;
    for(int i =0; i<4; i++){

        b = bread(1, PSASTART+(blockno)+i);
        // Copy page contents to b.data using memmove.
        memmove(b->data, victim_page + (i*BSIZE) , BSIZE);
        bwrite(b);
        brelse(b);
        psa_tracker[blockno] = true;

    }
    
    p->heap_tracker[block_tacker].startblock = blockno;
    p->heap_tracker[block_tacker].loaded = false;

    /* Unmap swapped out page */
    uvmunmap(p->pagetable, victim_page, 1, 0);
    kfree(kernel_page);
    
    /* Update the resident heap tracker. */
    p->resident_heap_pages--;
}

/* Retrieve faulted page from disk. */
void retrieve_page_from_disk(struct proc* p, uint64 uvaddr) {
    /* Find where the page is located in disk */
    int blockno = 0;

    for (int i = 0; i < MAXHEAP; i++) {
        if (p->heap_tracker[i].addr == uvaddr) {
            blockno = p->heap_tracker[i].startblock;
            break;
        }
    }

    /* Print statement. */
    print_retrieve_page(uvaddr, blockno);

    /* Create a kernel page to read memory temporarily into first. */
    char *kernel_page = kalloc();
    
    /* Read the disk block into temp kernel page. */
    struct buf* b;
    for(int i =0; i<4; i++){

        b = bread(1, PSASTART+(blockno)+i);
        // Copy page contents to b.data using memmove.
        memmove(kernel_page + (i*BSIZE), b->data , BSIZE);
        // bwrite(b);
        brelse(b);
        psa_tracker[blockno] = false;

    }

    /* Copy from temp kernel page to uvaddr (use copyout) */
    copyout(p->pagetable, uvaddr, kernel_page, PGSIZE);
    kfree(kernel_page);
}


void page_fault_handler(void) 
{
    int i, off, al_loaded;
    uint64 sz = 0;
    struct elfhdr elf;
    struct inode *ip;
    struct proghdr ph;
    /* Current process struct */
    struct proc *p = myproc();

    /* Track whether the heap page should be brought back from disk or not. */
    bool load_from_disk = false;

    uint64 stval_val = r_stval();
    uint64 r_stval_val = stval_val >> 12;

    /* Find faulting address. */
    uint64 faulting_addr = r_stval_val << 12;
    print_page_fault(p->name, faulting_addr);

    int tracker = 0;


    bool heap_fault = false;
    for (int i = 0; i < MAXHEAP; i++) {
        if (faulting_addr >= p->heap_tracker[i].addr && faulting_addr < (p->heap_tracker[i].addr + PGSIZE)) {
            heap_fault = true;
            tracker = i;
            break;
        
        }
    }


    /* Check if the fault address is a heap page. Use p->heap_tracker */
    if (heap_fault) {
        goto heap_handle;
    }

    /* If it came here, it is a page from the program binary that we must load. */


    begin_op();

    if((ip = namei(p->name)) == 0){
        end_op();
        return -1;
    }
    ilock(ip);

  // Check ELF header
    if(readi(ip, 0, (uint64)&elf, 0, sizeof(elf)) != sizeof(elf))
        goto out;

    if(elf.magic != ELF_MAGIC)
        goto out;

    for(i=0, off=elf.phoff; i<elf.phnum; i++, off+=sizeof(ph)){
    if(readi(ip, 0, (uint64)&ph, off, sizeof(ph)) != sizeof(ph))
      goto out;
    if(ph.type != ELF_PROG_LOAD)
      continue;
    if(ph.memsz < ph.filesz)
      goto out;
    if(ph.vaddr + ph.memsz < ph.vaddr)
      goto out;
    // if(ph.vaddr % PGSIZE != 0)
    //   goto out;

    if(ph.vaddr < stval_val && ph.vaddr+ph.memsz > stval_val){
        uint64 sz1;
        if((sz1 = uvmalloc(p->pagetable, faulting_addr, faulting_addr+PGSIZE, flags2perm(ph.flags))) == 0)
        goto out;
        sz = sz1;
        uint64 faulting_offset =  ph.off + faulting_addr - ph.vaddr;
        if(loadseg(p->pagetable, faulting_addr, ip, faulting_offset, PGSIZE) < 0)
        goto out;
        print_load_seg(faulting_addr, faulting_offset, PGSIZE);

        break;
    }
    // }else{
    //     while(sz < ph.vaddr + ph.memsz){
    //         sz += PGSIZE;
    // }
    }


    iunlockput(ip);
    end_op();
    ip = 0;
    
    /* Go to out, since the remainder of this code is for the heap. */
    goto out;

heap_handle:
    /* 2.4: Check if resident pages are more than heap pages. If yes, evict. */
    if (p->resident_heap_pages == MAXRESHEAP) {
        evict_page_to_disk(p);

        // if(al_loaded ==1){

        //     load_from_disk = true;
        // }
    }
    if(p->heap_tracker[tracker].startblock != -1){
        load_from_disk = true;
    

    }

    /* 2.4: Update the last load time for the loaded heap page in p->heap_tracker. */

    /* 2.4: Heap page was swapped to disk previously. We must load it from disk. */
    if (load_from_disk) {
        retrieve_page_from_disk(p, faulting_addr);
        p->heap_tracker[tracker].loaded = 1;
        p->heap_tracker[tracker].last_load_time = read_current_timestamp();
    }else{
        sz = uvmalloc(p->pagetable, faulting_addr, faulting_addr + PGSIZE, PTE_W);
        p->heap_tracker[tracker].loaded = 1;
        p->heap_tracker[tracker].last_load_time = read_current_timestamp();
        


    }
    
    /* 2.3: Map a heap page into the process' address space. (Hint: check growproc) */
    // if((sz = uvmalloc(p->pagetable, faulting_addr, faulting_addr + PGSIZE, PTE_W)) == 0) {

    //         return -1;
    // }else{
    //     p->heap_tracker[tracker].loaded = 1;
    //     p->heap_tracker[tracker].last_load_time = read_current_timestamp();
    // }


    

    /* 2.4: Update the last load time for the loaded heap page in p->heap_tracker. */

    /* 2.4: Heap page was swapped to disk previously. We must load it from disk. */
    // if (load_from_disk) {
    //     retrieve_page_from_disk(p, faulting_addr);
    // }

    /* Track that another heap page has been brought into memory. */
    p->resident_heap_pages++;

out:
    /* Flush stale page table entries. This is important to always do. */
    sfence_vma();
    return;
}
