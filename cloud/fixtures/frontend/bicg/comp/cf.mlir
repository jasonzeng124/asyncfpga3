module {
  func.func @bicg(%arg0: memref<900xi32>, %arg1: memref<30xi32>, %arg2: memref<30xi32>, %arg3: memref<30xi32>, %arg4: memref<30xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg2[%2] {handshake.name = "load0"} : memref<30xi32>
    %4 = arith.extui %0 : i32 to i64
    %5 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32, %3 : i32, i32)
  ^bb2(%6: i32, %7: i32):  // 2 preds: ^bb1, ^bb2
    %8 = arith.extui %6 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %9 = arith.muli %4, %c30_i64 : i64
    %10 = arith.addi %9, %8 : i64
    %11 = arith.index_cast %10 : i64 to index
    %12 = memref.load %arg0[%11] {handshake.name = "load1"} : memref<900xi32>
    %13 = arith.extui %6 : i32 to i64
    %14 = arith.index_cast %13 : i64 to index
    %15 = memref.load %arg1[%14] {handshake.name = "load2"} : memref<30xi32>
    %16 = arith.index_cast %5 : i64 to index
    %17 = memref.load %arg4[%16] {handshake.name = "load3"} : memref<30xi32>
    %18 = arith.muli %17, %12 : i32
    %19 = arith.addi %15, %18 : i32
    %20 = arith.extui %6 : i32 to i64
    %21 = arith.index_cast %20 : i64 to index
    memref.store %19, %arg1[%21] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<30xi32>
    %22 = arith.extui %6 : i32 to i64
    %23 = arith.index_cast %22 : i64 to index
    %24 = memref.load %arg3[%23] {handshake.name = "load5"} : memref<30xi32>
    %25 = arith.muli %12, %24 : i32
    %26 = arith.addi %7, %25 : i32
    %27 = arith.addi %6, %c1_i32 : i32
    %28 = arith.cmpi ult, %27, %c30_i32 : i32
    cf.cond_br %28, ^bb2(%27, %26 : i32, i32), ^bb3(%26 : i32)
  ^bb3(%29: i32):  // pred: ^bb2
    %30 = arith.extui %0 : i32 to i64
    %31 = arith.index_cast %30 : i64 to index
    memref.store %29, %arg2[%31] {handshake.name = "store6"} : memref<30xi32>
    %32 = arith.addi %0, %c1_i32 : i32
    %33 = arith.cmpi ult, %32, %c30_i32 : i32
    cf.cond_br %33, ^bb1(%32 : i32), ^bb4(%29 : i32)
  ^bb4(%34: i32):  // pred: ^bb3
    return %34 : i32
  }
}
