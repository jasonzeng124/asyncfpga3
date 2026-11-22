module {
  func.func @insertion_sort(%arg0: memref<30xi32> {handshake.arg_name = "A"}, %arg1: i32 {handshake.arg_name = "n"}) {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %0 = arith.cmpi sgt, %arg1, %c1_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c1_i32 : i32), ^bb5 {handshake.name = "cond_br0"}
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb4
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<30xi32>
    cf.br ^bb2(%1 : i32) {handshake.name = "br0"}
  ^bb2(%5: i32):  // 2 preds: ^bb1, ^bb3
    %c-1_i32 = arith.constant {handshake.name = "constant3"} -1 : i32
    %6 = arith.addi %5, %c-1_i32 {handshake.name = "addi0"} : i32
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i32 to index
    %8 = memref.load %arg0[%7] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<30xi32>
    %9 = arith.cmpi sgt, %8, %4 {handshake.name = "cmpi1"} : i32
    cf.cond_br %9, ^bb3, ^bb4(%5 : i32) {handshake.name = "cond_br1"}
  ^bb3:  // pred: ^bb2
    %c0_i32 = arith.constant {handshake.name = "constant4"} 0 : i32
    %c-1_i32_0 = arith.constant {handshake.name = "constant5"} -1 : i32
    %10 = arith.addi %5, %c-1_i32_0 {handshake.name = "addi1"} : i32
    %11 = arith.index_cast %10 {handshake.name = "index_cast2"} : i32 to index
    %12 = memref.load %arg0[%11] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : memref<30xi32>
    %13 = arith.index_cast %5 {handshake.name = "index_cast3"} : i32 to index
    memref.store %12, %arg0[%13] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<30xi32>
    %14 = arith.addi %5, %c-1_i32_0 {handshake.name = "addi2"} : i32
    %15 = arith.cmpi sgt, %14, %c0_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %15, ^bb2(%14 : i32), ^bb4(%c0_i32 : i32) {handshake.name = "cond_br2"}
  ^bb4(%16: i32):  // 2 preds: ^bb2, ^bb3
    %c1_i32_1 = arith.constant {handshake.name = "constant6"} 1 : i32
    %17 = arith.index_cast %16 {handshake.name = "index_cast4"} : i32 to index
    memref.store %4, %arg0[%17] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<30xi32>
    %18 = arith.addi %1, %c1_i32_1 {handshake.name = "addi3"} : i32
    %19 = arith.cmpi slt, %18, %arg1 {handshake.name = "cmpi3"} : i32
    cf.cond_br %19, ^bb1(%18 : i32), ^bb5 {handshake.name = "cond_br3"}
  ^bb5:  // 2 preds: ^bb0, ^bb4
    return {handshake.name = "return0"}
  }
}

