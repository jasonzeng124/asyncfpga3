module {
  func.func @test_memory_1(%arg0: memref<4xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant3"} 1 : i32
    %c5_i32 = arith.constant {handshake.name = "constant4"} 5 : i32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<4xi32>
    %5 = arith.addi %4, %c5_i32 {handshake.name = "addi0"} : i32
    %6 = arith.extui %1 {handshake.name = "extui1"} : i32 to i64
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i64 to index
    memref.store %5, %arg0[%7] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : memref<4xi32>
    %8 = arith.addi %1, %c1_i32 {handshake.name = "addi1"} : i32
    %9 = arith.cmpi slt, %8, %arg1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %9, ^bb1(%8 : i32), ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"}
  }
}

