module {
  func.func @test_unroll(%arg0: memref<20xi32> {handshake.arg_name = "A"}, %arg1: memref<20xi32> {handshake.arg_name = "B"}, %arg2: memref<20xi32> {handshake.arg_name = "C"}, %arg3: memref<20xi32> {handshake.arg_name = "result"}) {
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %alloca = memref.alloca() {handshake.name = "alloca0"} : memref<20xi32>
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c20_i32 = arith.constant {handshake.name = "constant2"} 20 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant4"} 0 : i32
    %c1_i32 = arith.constant {handshake.name = "constant5"} 1 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<20xi32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast1"} : i64 to index
    %6 = memref.load %arg1[%5] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<20xi32>
    %7 = arith.muli %3, %6 {handshake.name = "muli0"} : i32
    %8 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast2"} : i64 to index
    memref.store %7, %alloca[%9] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : memref<20xi32>
    %10 = arith.addi %0, %c1_i32 {handshake.name = "addi1"} : i32
    %11 = arith.cmpi ult, %10, %c20_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %11, ^bb1(%10 : i32), ^bb2(%c0_i32_0 : i32) {handshake.name = "cond_br0"}
  ^bb2(%12: i32):  // 2 preds: ^bb1, ^bb2
    %c20_i32_1 = arith.constant {handshake.name = "constant6"} 20 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant7"} 1 : i32
    %13 = arith.extui %12 {handshake.name = "extui3"} : i32 to i64
    %14 = arith.index_cast %13 {handshake.name = "index_cast3"} : i64 to index
    %15 = memref.load %alloca[%14] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load3"} : memref<20xi32>
    %16 = arith.extui %12 {handshake.name = "extui4"} : i32 to i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast4"} : i64 to index
    %18 = memref.load %arg2[%17] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : memref<20xi32>
    %19 = arith.muli %15, %18 {handshake.name = "muli3"} : i32
    %20 = arith.extui %12 {handshake.name = "extui5"} : i32 to i64
    %21 = arith.index_cast %20 {handshake.name = "index_cast5"} : i64 to index
    memref.store %19, %arg3[%21] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store5"} : memref<20xi32>
    %22 = arith.addi %12, %c1_i32_2 {handshake.name = "addi3"} : i32
    %23 = arith.cmpi ult, %22, %c20_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %23, ^bb2(%22 : i32), ^bb3 {handshake.name = "cond_br1"}
  ^bb3:  // pred: ^bb2
    return {handshake.name = "return0"}
  }
}

