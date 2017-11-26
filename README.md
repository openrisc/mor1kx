# *mor1kx* - an OpenRISC processor IP core

## The Basics

This repository contains an OpenRISC 1000 compliant processor IP core.

It is written in Verilog HDL.

This repository only contains the IP source code and some documentation. For
a verification environment, please see other projects.

## Documentation

The documentation is located in the doc/ directory.

It is asciidoc format, and there's a makefile in there to build HTML or PDF. To
build the HTML documentation, run the following in the doc/ directory:

```
  make html
```

## License

It is licensed under the Open Hardware Description License (OHDL). For
details please see the LICENSE file or http://juliusbaxter.net/ohdl/

## Configuration

The mor1kx CPU is very configurable to allow your to customize the core to your
exact needs. The tables explain explain how each parameter can be configure,
what the configuration a does and why you might want to use it.

*Note** *Below the *Usage* field is populated to indicate if a certain application such
as running Linux requires a setting different than the default value.*

### Basic parameters

|Parameter|Description|Default|Values|Usage?|
|---------|-----------|-------|------|------|
|OPTION_OPERAND_WIDTH|Specifies the CPU data and address widths|32|32,64,etc| |
|OPTION_CPU0|Specifies the CPU pipeline core|`CAPPUCCINO`|`CAPPUCCINO` `ESPRESSO` `PRONTO_ESPRESSO`|`CAPPUCCINO` for Linux|
|OPTION_RESET_PC|Specifies the program counter upon reset|`0x100`|n| |

### Caching parameters

|Parameter|Description|Default|Values|Usage?|
|---------|-----------|-------|------|------|
|FEATURE_DATACACHE|Enable memory access data caching|`NONE`|`ENABLED` `NONE`| |
|OPTION_DCACHE_BLOCK_WIDTH|Specifies the address width of a cache block|5|`n`| |
|OPTION_DCACHE_SET_WIDTH|Specifies the set address width|9|`n`| |
|OPTION_DCACHE_WAYS|Specifies the number of blocks per set|2|`n`| |
|OPTION_DCACHE_LIMIT_WIDTH|Specifies the maximum address width|32|`n`| |
|OPTION_DCACHE_SNOOP|Enable bus snooping for cache coherency|`NONE`|`ENABLED` `NONE`|Linux SMP|
|FEATURE_INSTRUCTIONCACHE|Enable memory access instruction caching|`NONE`|`ENABLED` `NONE`| |
|OPTION_ICACHE_BLOCK_WIDTH|Specifies the address width of a cache block|5|`n`| |
|OPTION_ICACHE_SET_WIDTH|Specifies the set address width|9|`n`| |
|OPTION_ICACHE_WAYS|Specifies the number of blocks per set|2|`n`| |
|OPTION_ICACHE_LIMIT_WIDTH|specifies the maximum address width|32|`n`| |

### Memory Management Unit (MMU) parameters

|Parameter|Description|Default|Values|Usage?|
|---------|-----------|-------|------|------|
|FEATURE_DMMU|Enable the data bus MMU|`NONE`|`ENABLED` `NONE`|Linux expects `ENABLED`|
|FEATURE_DMMU_HW_TLB_RELOAD|Enable hardware TLB reload|`NONE`|`ENABLED` `NONE`|Linux expects `NONE`|
|OPTION_DMMU_SET_WIDTH|Specifies the set address width|6|`n`| |
|OPTION_DMMU_WAYS|Specifies the number of ways per set|1|`n`| |
|FEATURE_IMMU|Enable the instruction bus MMU|`NONE`|`ENABLED` `NONE`|Linux expects `ENABLED`|
|FEATURE_IMMU_HW_TLB_RELOAD|Enable hardware TLB reload|`NONE`|`ENABLED` `NONE`|Linux expects `NONE`|
|OPTION_IMMU_SET_WIDTH|Specifies the set address width|6|`n`| |
|OPTION_IMMU_WAYS|Specifies the number of ways per set|1|`n`| |

### System bus parameters

|Parameter|Description|Default|Values|Usage?|
|---------|-----------|-------|------|------|
|FEATURE_STORE_BUFFER|Enables the load store unit store buffer|`ENABLED`|`ENABLED` `NONE`|Large footprint|
|OPTION_STORE_BUFFER_DEPTH_WIDTH|Specifies the load store unit store buffer depth|8|1-n| |
|BUS_IF_TYPE|Specify the bus interface type|`WISHBONE32`|`WISHBONE32`| |
|IBUS_WB_TYPE|Specify the Instruction bus interface type option|`B3_READ_BURSTING`|`B3_READ_BURSTING` `B3_REGISTERED_FEEDBACK` `CLASSIC`| |
|DBUS_WB_TYPE|Specify the Data bus interface type option|`CLASSIC`|`B3_READ_BURSTING` `B3_REGISTERED_FEEDBACK` `CLASSIC`| |

### Hardware unit configuration parameters

|Parameter|Description|Default|Values|Usage?|
|---------|-----------|-------|------|------|
|FEATURE_TRACEPORT_EXEC|Enables the traceport hardware interface|`NONE`|`ENABLED` `NONE`|Verilator|
|FEATURE_DEBUGUNIT|Enables hardware breakpoints and advanced debug unit interface|`NONE`|`ENABLED` `NONE`|OpenOCD|
|FEATURE_PERFCOUNTERS|Enables the performance counters unit|`NONE`|`ENABLED` `NONE`| |
|OPTION_PERFCOUNTERS_NUM|Specifies the number of performance counters to generate|0|n| |
|FEATURE_TIMER|Enable the internal OpenRISC timer|`ENABLED`|`ENABLED` `NONE`| |
|FEATURE_PIC|Enable the internal OpenRISC PIC|`ENABLED`|`ENABLED` `NONE`| |
|OPTION_PIC_TRIGGER|Specifies the PIC trigger mode|`LEVEL`|`LEVEL` `EDGE` `LATCHED_LEVEL`| |
|OPTION_PIC_NMI_WIDTH|Specifies non maskable interrupts width, starting at 0, these interrupts will not be reset or maskable|0|0-32| |
|OPTION_RF_CLEAR_ON_INIT|Enables clearing all registers on initialization|0|0,1| |
|OPTION_RF_NUM_SHADOW_GPR|Specifies the number of shadow register files|0|0-16|Set `>=1` for Linux SMP|
|OPTION_RF_ADDR_WIDTH|Specifies the address width of the register file|5|5| |
|OPTION_RF_WORDS|Specifies the number of registers in the register file|32|32| |
|FEATURE_FASTCONTEXTS|Enable fast context switching of register sets|`NONE`|`ENABLED` `NONE`| |
|FEATURE_MULTICORE|Enables the `coreid` and `numcores` SPR registers|`NONE`|`ENABLED` `NONE`|Linux SMP|
|FEATURE_FPU|Enables the FPU, for cappuccino pipeline only|`NONE`|`ENABLED` `NONE`| |

### Exception handling options

|Parameter|Description|Default|Values|Usage?|
|---------|-----------|-------|------|------|
|FEATURE_DSX|Enable setting the `SR[DSX]` flag when raising exceptions in a delay slot|`ENABLED`|`ENABLED` `NONE`| |
|FEATURE_RANGE|Enable checking and raising range exceptions|`ENABLED`|`ENABLED` `NONE`| |
|FEATURE_OVERFLOW|Enable checking and raising overflow exceptions|`ENABLED`|`ENABLED` `NONE`| |

### ALU configuration options

|Parameter|Description|Default|Values|Usage?|
|---------|-----------|-------|------|------|
|FEATURE_MULTIPLIER|Specify the multiplier implementation|`THREESTAGE`|`THREESTAGE` `PIPELINED` `SERIAL` `SIMULATION` `NONE`| |
|FEATURE_DIVIDER|Specify the divider implementation|`SERIAL`|`SERIAL` `SIMULATION` `NONE`| |
|OPTION_SHIFTER|Specify the shifter implementation|`BARREL`|`BARREL` `SERIAL`| |
|FEATURE_CARRY_FLAG|Enables checking and setting the carry flag|`ENABLED`|`ENABLED` `NONE`| |

### Instruction enabling options

|Parameter|Description|Default|Values|Usage?|
|---------|-----------|-------|------|------|
|FEATURE_MAC|Enables the `l.mac*` multiply accumulate instructions|`NONE`|`ENABLED` `NONE`| |
|FEATURE_SYSCALL|Enables the 'l.sys` OS syscall instruction|`ENABLED`|`ENABLED` `NONE`| |
|FEATURE_TRAP|Enables the `l.trap` instruction|`ENABLED`|`ENABLED` `NONE`|GDB|
|FEATURE_ADDC|Enables the `l.addc` add with `carry` flag instruction|`ENABLED`|`ENABLED` `NONE`| |
|FEATURE_SRA|Enables the `l.sra` shirt right arithmetic instruction|`ENABLED`|`ENABLED` `NONE`| |
|FEATURE_ROR|Enables the `l.ror*` rotate right instructions|`NONE`|`ENABLED` `NONE`| |
|FEATURE_EXT|Enables the `l.ext*` sign extend instructions|`NONE`|`ENABLED` `NONE`| |
|FEATURE_CMOV|Enables the `l.cmov` conditional move instruction|`ENABLED`|`ENABLED` `NONE`| |
|FEATURE_FFL1|Enables the `l.f[fl]1` find first/last set bit instructions|`ENABLED`|`ENABLED` `NONE`|Linux|
|FEATURE_ATOMIC|Enables the `l.lwa` and `l.swa` atomic instructions|`ENABLED`|`ENABLED` `NONE`|Linux SMP|
|FEATURE_CUST1|Enables the `l.cust*` custom instruction|`NONE`|`ENABLED` `NONE`| |
|FEATURE_CUST2|Enables the `l.cust*` custom instruction|`NONE`|`ENABLED` `NONE`| |
|FEATURE_CUST3|Enables the `l.cust*` custom instruction|`NONE`|`ENABLED` `NONE`| |
|FEATURE_CUST4|Enables the `l.cust*` custom instruction|`NONE`|`ENABLED` `NONE`| |
|FEATURE_CUST5|Enables the `l.cust*` custom instruction|`NONE`|`ENABLED` `NONE`| |
|FEATURE_CUST6|Enables the `l.cust*` custom instruction|`NONE`|`ENABLED` `NONE`| |
|FEATURE_CUST7|Enables the `l.cust*` custom instruction|`NONE`|`ENABLED` `NONE`| |
|FEATURE_CUST8|Enables the `l.cust*` custom instruction|`NONE`|`ENABLED` `NONE`| |

