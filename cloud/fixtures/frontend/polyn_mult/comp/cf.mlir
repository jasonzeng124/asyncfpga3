module {
  func.func @polyn_mult(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: memref<100xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c100_i32 = arith.constant 100 : i32
    %c1_i32 = arith.constant 1 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    memref.store %c0_i32, %arg2[%2] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : memref<100xi32>
    %3 = arith.subi %c100_i32, %0 : i32
    %4 = arith.cmpi ult, %c1_i32, %3 : i32
    cf.cond_br %4, ^bb2(%c1_i32 : i32), ^bb3
  ^bb2(%5: i32):  // 2 preds: ^bb1, ^bb2
    %6 = arith.addi %0, %5 : i32
    %7 = arith.extui %6 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load1"} : memref<100xi32>
    %10 = arith.subi %c100_i32, %5 : i32
    %11 = arith.extui %10 : i32 to i64
    %12 = arith.index_cast %11 : i64 to index
    %13 = memref.load %arg1[%12] {handshake.name = "load2"} : memref<100xi32>
    %14 = arith.muli %9, %13 : i32
    %15 = arith.extui %0 : i32 to i64
    %16 = arith.index_cast %15 : i64 to index
    %17 = memref.load %arg2[%16] {handshake.name = "load3"} : memref<100xi32>
    %18 = arith.addi %17, %14 : i32
    %19 = arith.index_cast %15 : i64 to index
    memref.store %18, %arg2[%19] {handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<100xi32>
    %20 = arith.addi %5, %c1_i32 : i32
    %21 = arith.cmpi ult, %20, %3 : i32
    cf.cond_br %21, ^bb2(%20 : i32), ^bb3
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %22 = arith.addi %0, %c1_i32 : i32
    cf.br ^bb4(%c0_i32 : i32)
  ^bb4(%23: i32):  // 2 preds: ^bb3, ^bb4
    %24 = arith.subi %0, %23 : i32
    %25 = arith.extui %24 : i32 to i64
    %26 = arith.index_cast %25 : i64 to index
    %27 = memref.load %arg0[%26] {handshake.name = "load5"} : memref<100xi32>
    %28 = arith.extui %23 : i32 to i64
    %29 = arith.index_cast %28 : i64 to index
    %30 = memref.load %arg1[%29] {handshake.name = "load6"} : memref<100xi32>
    %31 = arith.muli %27, %30 : i32
    %32 = arith.extui %0 : i32 to i64
    %33 = arith.index_cast %32 : i64 to index
    %34 = memref.load %arg2[%33] {handshake.name = "load7"} : memref<100xi32>
    %35 = arith.addi %34, %31 : i32
    %36 = arith.index_cast %32 : i64 to index
    memref.store %35, %arg2[%36] {handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store8"} : memref<100xi32>
    %37 = arith.addi %23, %c1_i32 : i32
    %38 = arith.cmpi ult, %37, %22 : i32
    cf.cond_br %38, ^bb4(%37 : i32), ^bb5(%37 : i32)
  ^bb5(%39: i32):  // pred: ^bb4
    %40 = arith.addi %39, %0 : i32
    %41 = arith.addi %0, %c1_i32 : i32
    %42 = arith.cmpi ult, %41, %c100_i32 : i32
    cf.cond_br %42, ^bb1(%41 : i32), ^bb6(%40 : i32)
  ^bb6(%43: i32):  // pred: ^bb5
    return %43 : i32
  }
}
