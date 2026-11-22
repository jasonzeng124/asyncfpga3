module {
  func.func @path_profiling(%arg0: memref<20xi32> {handshake.arg_name = "a"}, %arg1: memref<20xi32> {handshake.arg_name = "b"}, %arg2: memref<20xi32> {handshake.arg_name = "var"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb7
    %c1_i32 = arith.constant {handshake.name = "constant5"} 1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant6"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg2[%2] {handshake.name = "load0"} : memref<20xi32>
    %4 = arith.andi %3, %c1_i32 {handshake.name = "andi0"} : i32
    %5 = arith.cmpi eq, %4, %c0_i32_0 {handshake.name = "cmpi0"} : i32
    cf.cond_br %5, ^bb2, ^bb3 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %c2_i32 = arith.constant {handshake.name = "constant7"} 2 : i32
    %6 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i64 to index
    memref.store %c2_i32, %arg0[%7] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<20xi32>
    cf.br ^bb4 {handshake.name = "br1"}
  ^bb3:  // pred: ^bb1
    %c3_i32 = arith.constant {handshake.name = "constant8"} 3 : i32
    %8 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast2"} : i64 to index
    memref.store %c3_i32, %arg0[%9] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<20xi32>
    cf.br ^bb4 {handshake.name = "br2"}
  ^bb4:  // 2 preds: ^bb2, ^bb3
    %c3_i32_1 = arith.constant {handshake.name = "constant9"} 3 : i32
    %c0_i32_2 = arith.constant {handshake.name = "constant10"} 0 : i32
    %10 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast3"} : i64 to index
    %12 = memref.load %arg2[%11] {handshake.name = "load3"} : memref<20xi32>
    %13 = arith.remsi %12, %c3_i32_1 {handshake.name = "remsi0"} : i32
    %14 = arith.cmpi eq, %13, %c0_i32_2 {handshake.name = "cmpi1"} : i32
    cf.cond_br %14, ^bb5, ^bb6 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c2_i32_3 = arith.constant {handshake.name = "constant11"} 2 : i32
    %15 = arith.extui %0 {handshake.name = "extui4"} : i32 to i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast4"} : i64 to index
    memref.store %c2_i32_3, %arg1[%16] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<20xi32>
    cf.br ^bb7 {handshake.name = "br3"}
  ^bb6:  // pred: ^bb4
    %c3_i32_4 = arith.constant {handshake.name = "constant12"} 3 : i32
    %17 = arith.extui %0 {handshake.name = "extui5"} : i32 to i64
    %18 = arith.index_cast %17 {handshake.name = "index_cast5"} : i64 to index
    memref.store %c3_i32_4, %arg1[%18] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<20xi32>
    cf.br ^bb7 {handshake.name = "br4"}
  ^bb7:  // 2 preds: ^bb5, ^bb6
    %c20_i32 = arith.constant {handshake.name = "constant13"} 20 : i32
    %c1_i32_5 = arith.constant {handshake.name = "constant14"} 1 : i32
    %19 = arith.addi %0, %c1_i32_5 {handshake.name = "addi0"} : i32
    %20 = arith.cmpi ult, %19, %c20_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %20, ^bb1(%19 : i32), ^bb8 {handshake.name = "cond_br2"}
  ^bb8:  // pred: ^bb7
    return {handshake.name = "return0"}
  }
}

