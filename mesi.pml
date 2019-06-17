// model of MESI protocol. Each CPU consists of 3 processes: 
// CPU - generates reads and writes for the memory subsystem, sends them to cache
// cache - serves the reads and writes from cpu, modifies the cache memory and its state
// snooper - listens on the memory bus for messages from other CPUs
//           and modifies the cache state accordingly
// There is one global process which represents main memory.

#define PROC_COUNT 2
#define CACHE_SIZE 2
#define MEMORY_SIZE 4
#define VALUE_RANGE 100
#define ADDRESS_T byte
#define VALUE_T byte
#define ID_T bit

mtype:bus_msg =
{
    bus_read,
    bus_readx,
    bus_upgrade,
    bus_flush,
    bus_flushopt
    bus_na
}

mtype:leader_msg =
{
    leader_na,
    leader_av
}

mtype:cpu_msg =
{
    proc_read,
    proc_write
}

mtype:mesi = {
    modified,
    exclusive,
    shared,
    invalid
}

chan cpu_chan[PROC_COUNT] = [0] of {mtype:cpu_msg, ADDRESS_T, VALUE_T };
chan bus_chan[PROC_COUNT] = [0] of {mtype:bus_msg, ID_T, ADDRESS_T, VALUE_T }
chan leader_chan[PROC_COUNT] = [0] of {mtype:leader_msg, ID_T}
chan memory_chan = [0] of {mtype:bus_msg, ID_T, ADDRESS_T, VALUE_T };
bool in_way

typedef cache_t
{
    bool lock = 0
    bool op_waiting = 0
    bool snooper_waiting = 0
    mtype:mesi state[MEMORY_SIZE]
    VALUE_T val[MEMORY_SIZE]
    chan used_queue = [CACHE_SIZE] of { ADDRESS_T }
}

cache_t caches[PROC_COUNT]

VALUE_T memory[MEMORY_SIZE]

proctype cpu(ID_T id)
{
    ADDRESS_T addr
    VALUE_T val
    do
    :: select(addr : 0 .. MEMORY_SIZE-1); cpu_chan[id]!proc_read,addr,0
    :: select(addr : 0 .. MEMORY_SIZE-1); select(val : 0 .. VALUE_RANGE-1); cpu_chan[id]!proc_write,addr,val
    od
}


inline acquire_lock_and_send_bus_msg(msg, id, addr, val)
{
    int index
    atomic
    {
        printf("clock %d\n", id)
        caches[id].lock == 0 && caches[id].op_waiting == 0 && caches[id].snooper_waiting == 0
        caches[id].lock = 1
        printf("clocked %d\n", id)
        for(index : 0 .. PROC_COUNT-1)
        {
            if
            :: (index != id) -> caches[index].op_waiting = 1
            :: else -> skip
            fi
        }
        for(index : 0 .. PROC_COUNT-1)
        {
            if
            :: (index != id) -> printf("staying %d\n", index); bus_chan[index]!msg,id,addr,val
            :: else -> skip
            fi
        }
        for(index : 0 .. PROC_COUNT-1)
        {
            if
            :: (index != id) -> caches[index].op_waiting = 0
            :: else -> skip
            fi
        }
        printf("read %d %d\n", id, addr)
    
    }
}

inline update_used_queue(id, addr)
{
    ADDRESS_T throw_addr
    if
    :: full(caches[id].used_queue) ->
        
        caches[id].used_queue?throw_addr
        if
        :: caches[id].state[throw_addr] == modified ->
            {
                printf("uinway %d\n", id)
                in_way = true
                memory_chan!bus_flush,id,throw_addr,caches[id].val[throw_addr]
            }
        :: else -> skip
        fi
        caches[id].state[throw_addr] = invalid
        
    :: nfull(caches[id].used_queue) -> skip
    fi
    
    caches[id].used_queue!addr
}


proctype cache(ID_T id) {
    mtype:msg m
    ADDRESS_T addr
    VALUE_T val
    
    do
    :: cpu_chan[id]?proc_read,addr,_ ->
        if 
        :: (caches[id].state[addr] != invalid) //cache hit
        :: else -> 
            printf("r %d\n", id)
            acquire_lock_and_send_bus_msg(bus_read, id, addr, 0)
            byte av_count = 0
            byte all_count = 0
            ID_T rid
            bool sent_request = false
            bool received_request = false
            
            do
            :: all_count == PROC_COUNT - 1 -> break
            :: all_count < PROC_COUNT - 1 ->
                if 
                :: leader_chan[id]?leader_av,rid ->
                    {
                        if
                        :: sent_request -> leader_chan[rid]!leader_na,id
                        :: else -> leader_chan[rid]!leader_av,id; sent_request = true;
                        fi
                        av_count++;
                        all_count++;
                    } 
                :: leader_chan[id]?leader_na,_ -> all_count++
                fi
            od
            
            if
            :: av_count == 0 -> memory_chan!bus_read,id,addr,0
            :: else -> skip
            fi
            
            
            bus_chan[id]?bus_flushopt,_,_,val
            
            update_used_queue(id, addr)
            
            if
            :: av_count == 0 -> caches[id].state[addr] = exclusive
            :: av_count >= 0 -> caches[id].state[addr] = shared
            fi
            caches[id].val[addr] = val
            
            d_step{
            printf("cunlock %d\n", id)
            caches[id].lock = 0}
        fi
    :: cpu_chan[id]?proc_write,addr,val ->
        printf("w %d\n", id)
        acquire_lock_and_send_bus_msg(bus_readx, id, addr, 0)
        if
        :: caches[id].state[addr] == exclusive ->
            caches[id].state[addr] = modified
            caches[id].val[addr] = val;
            
        :: caches[id].state[addr] == modified ->
            caches[id].val[addr] = val
            
        :: caches[id].state[addr] == shared ->
            caches[id].state[addr] = modified
            caches[id].val[addr] = val;
            
        :: caches[id].state[addr] == invalid ->
            update_used_queue(id, addr)
            caches[id].state[addr] = modified
            caches[id].val[addr] = val;
        fi
        
        caches[id].lock = 0
        printf("wunlock %d\n", id)
         printf("write %d %d %d\n", id, addr, val)
    od
}

proctype snooper(ID_T id)
{
    ID_T rid
    ADDRESS_T addr
    VALUE_T val
    do
    :: atomic { bus_chan[id]?bus_read,rid,addr,_ ->
                
            printf("slock %d\n", id)
            caches[id].snooper_waiting = 1
            caches[id].lock == 0
            caches[id].lock = 1
            caches[id].snooper_waiting = 0
            printf("slocked %d\n", id)
        }
            
        if
        :: caches[id].state[addr] == exclusive ->
            {
                caches[id].state[addr] = shared
                leader_chan[rid]!leader_av,id
                leader_chan[id]?leader_av,_
                bus_chan[rid]!bus_flushopt, id, addr, caches[id].val[addr]
            }
        :: caches[id].state[addr] == modified ->
            {
                in_way = true
                memory_chan!bus_flush, id, addr, caches[id].val[addr]
                caches[id].state[addr] = shared
                leader_chan[rid]!leader_av,id
                leader_chan[id]?leader_av,_
                bus_chan[rid]!bus_flushopt, id, addr, caches[id].val[addr]
                
            }
        :: caches[id].state[addr] == shared ->    
            {
                leader_chan[rid]!leader_av,id
                
                if
                :: leader_chan[id]?leader_av,rid -> bus_chan[rid]!bus_flushopt, id, addr, caches[id].val[addr]
                :: leader_chan[id]?leader_na,_
                fi
            }        
        :: caches[id].state[addr] == invalid ->
            {
                printf("rid %d %d\n",id, rid)
                leader_chan[rid]!leader_na,id
            }
        fi
        
        printf("sunlock %d\n", id)
        caches[id].lock = 0

    :: atomic { bus_chan[id]?bus_readx,rid,addr,_ ->
            printf("wslock %d\n", id)
            caches[id].snooper_waiting = 1
            caches[id].lock == 0
            caches[id].lock = 1
            printf("wslocked %d", id)
            caches[id].snooper_waiting = 0
        }
        
        if
        :: caches[id].state[addr] == invalid -> skip
        :: else ->
            if
            :: caches[id].state[addr] == modified ->
                    printf("winway %d\n", id)
                    in_way = true
                    memory_chan!bus_flush,id,addr,caches[id].val[addr]
            :: else -> skip
            fi
            caches[id].used_queue??eval(addr)
            caches[id].state[addr] = invalid
        fi
        printf("wsunlocku %d\n", id)
        caches[id].lock = 0
    od
}

proctype main_memory()
{
    ID_T rid
    ID_T id
    ADDRESS_T addr
    VALUE_T val
    
    do
    :: atomic {memory_chan?bus_read,rid,addr,_ ->
            
            bus_chan[rid]!bus_flushopt,255,addr,memory[addr]
            }
    :: atomic {memory_chan?bus_flush,_,addr,val ->
    {
            printf("written %d %d\n", addr, val)
            memory[addr] = val
            in_way = false
            
    }
            }
    od
}

init
{
    byte i
    byte j
    VALUE_T val
    for(i : 0 .. MEMORY_SIZE-1)
    {
        for(j : 0 .. PROC_COUNT-1)
        {
            caches[j].state[i] = invalid
        }
        select(val: 0 .. VALUE_RANGE-1)
        memory[i] = val+1;
    }
    
    run correctness()
    
    for(i : 0 .. PROC_COUNT-1)
    {
        run cache(i);
        run cpu(i);
        run snooper(i);
    }
    run main_memory();
    
}



byte never_id
byte never_ad = 0
mtype:mesi never_seen = invalid 
bool correct = true
proctype correctness()
{
s:  do
    :: atomic {
            for(never_id : 0 .. PROC_COUNT - 1)
            {
                if
                :: caches[never_id].lock == 0
                :: else -> goto s
                fi
            }
            
            for(never_ad : 0 .. CACHE_SIZE - 1)
            {
                never_seen = invalid
                for(never_id : 0 .. PROC_COUNT - 1)
                {
                    if
                    :: never_seen == invalid && caches[never_id].state[never_ad] != invalid -> never_seen = caches[never_id].state[never_ad]
                    :: never_seen == exclusive && caches[never_id].state[never_ad] != invalid -> printf("1"); correct = false
                    :: never_seen == modified && caches[never_id].state[never_ad] != invalid -> printf("2"); correct = false
                    :: (never_seen == shared &&
                        caches[never_id].state[never_ad] != invalid &&
                        caches[never_id].state[never_ad] != shared) -> printf("3"); correct = false
                    :: caches[never_id].state[never_ad] != modified && caches[never_id].state[never_ad] != invalid && caches[never_id].val[never_ad] != memory[never_ad] -> printf("4"); correct = false
                    :: else -> skip
                    fi
                }
            }
            
        }
    od
}

ltl { [] correct}