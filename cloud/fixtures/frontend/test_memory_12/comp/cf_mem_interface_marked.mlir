module {
  func.func @test_memory_12(%arg0: memref<4xi32> {handshake.arg_name = "a"}) {
    %c2 = arith.constant {handshake.name = "constant3"} 2 : index
    %c1 = arith.constant {handshake.name = "constant5"} 1 : index
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c1_i32 = arith.constant {handshake.name = "constant2"} 1 : i32
    %c2_i32 = arith.constant {handshake.name = "constant4"} 2 : i32
    %c0 = arith.constant {handshake.name = "constant8"} 0 : index
    memref.store %c0_i32, %arg0[%c0] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store0"} : memref<4xi32>
    memref.store %c1_i32, %arg0[%c1] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : memref<4xi32>
    memref.store %c2_i32, %arg0[%c2] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : memref<4xi32>
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c1_i32_0 = arith.constant {handshake.name = "constant9"} 1 : i32
    %c0_i32_1 = arith.constant {handshake.name = "constant10"} 0 : i32
    %1 = arith.andi %0, %c1_i32_0 {handshake.name = "andi0"} : i32
    %2 = arith.cmpi eq, %1, %c0_i32_1 {handshake.name = "cmpi0"} : i32
    cf.cond_br %2, ^bb3, ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %c3_i32 = arith.constant {handshake.name = "constant11"} 3 : i32
    %c3 = arith.constant {handshake.name = "constant12"} 3 : index
    memref.store %c3_i32, %arg0[%c3] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store3"} : memref<4xi32>
    cf.br ^bb3 {handshake.name = "br1"}
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %c4_i32 = arith.constant {handshake.name = "constant13"} 4 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant14"} 1 : i32
    %3 = arith.addi %0, %c1_i32_2 {handshake.name = "addi0"} : i32
    %4 = arith.cmpi ult, %3, %c4_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %4, ^bb1(%3 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

