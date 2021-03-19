// OpenPiton L15 defines

`define  L15_LOAD_RQ     = 5'b00000, // load request
`define  L15_IMISS_RQ    = 5'b10000, // instruction fill request
`define  L15_STORE_RQ    = 5'b00001, // store request
`define  L15_ATOMIC_RQ   = 5'b00110, // atomic op
`define  //L15_CAS1_RQ     = 5'b00010, // compare and swap1 packet (OpenSparc atomics)
`define  //L15_CAS2_RQ     = 5'b00011, // compare and swap2 packet (OpenSparc atomics)
`define  //L15_SWAP_RQ     = 5'b00110, // swap packet (OpenSparc atomics)
`define  L15_STRLOAD_RQ  = 5'b00100, // unused
`define  L15_STRST_RQ    = 5'b00101, // unused
`define  L15_STQ_RQ      = 5'b00111, // unused
`define  L15_INT_RQ      = 5'b01001, // interrupt request
`define  L15_FWD_RQ      = 5'b01101, // unused
`define  L15_FWD_RPY     = 5'b01110, // unused
`define  L15_RSVD_RQ     = 5'b11111  // unused

`define  L15_LOAD_RET               = 4'b0000, // load packet
`define  // L15_INV_RET                = 4'b0011, // invalidate packet, not unique...
`define  L15_ST_ACK                 = 4'b0100, // store ack packet
`define  //L15_AT_ACK                 = 4'b0011, // unused, not unique...
`define  L15_INT_RET                = 4'b0111, // interrupt packet
`define  L15_TEST_RET               = 4'b0101, // unused
`define  L15_FP_RET                 = 4'b1000, // unused
`define  L15_IFILL_RET              = 4'b0001, // instruction fill packet
`define  L15_EVICT_REQ              = 4'b0011, // eviction request
`define  L15_ERR_RET                = 4'b1100, // unused
`define  L15_STRLOAD_RET            = 4'b0010, // unused
`define  L15_STRST_ACK              = 4'b0110, // unused
`define  L15_FWD_RQ_RET             = 4'b1010, // unused
`define  L15_FWD_RPY_RET            = 4'b1011, // unused
`define  L15_RSVD_RET               = 4'b1111, // unused
`define  L15_CPX_RESTYPE_ATOMIC_RES = 4'b1110  // custom type for atomic responses
