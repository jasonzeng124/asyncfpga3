module {
  func.func @test_memory_10(%arg0: memref<4xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}) {
    %c-1_i32 = arith.constant {handshake.name = "constant0"} -1 : i32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %0 = arith.addi %arg1, %c-1_i32 {handshake.name = "addi0"} : i32
    %1 = arith.cmpi sgt, %0, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %1, ^bb1(%c0_i32 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb1(%2: i32):  // 2 preds: ^bb0, ^bb1
    %c5_i32 = arith.constant {handshake.name = "constant4"} 5 : i32
    %c1_i32 = arith.constant {handshake.name = "constant5"} 1 : i32
    %3 = arith.extui %2 {handshake.name = "extui0"} : i32 to i64
    %4 = arith.index_cast %3 {handshake.name = "index_cast0"} : i64 to index
    %5 = memref.load %arg0[%4] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<4xi32>
    %6 = arith.addi %2, %c1_i32 {handshake.name = "addi1"} : i32
    %7 = arith.extui %6 {handshake.name = "extui1"} : i32 to i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast1"} : i64 to index
    %9 = memref.load %arg0[%8] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<4xi32>
    %10 = arith.addi %5, %9 {handshake.name = "addi2"} : i32
    %11 = arith.addi %10, %c5_i32 {handshake.name = "addi3"} : i32
    %12 = arith.extui %2 {handshake.name = "extui2"} : i32 to i64
    %13 = arith.index_cast %12 {handshake.name = "index_cast2"} : i64 to index
    memref.store %11, %arg0[%13] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : memref<4xi32>
    %14 = arith.addi %2, %c1_i32 {handshake.name = "addi4"} : i32
    %15 = arith.cmpi slt, %14, %0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %15, ^bb1(%14 : i32), ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"}
  }
}

