module {
  func.func @trisolv(%arg0: memref<1000xi32>, %arg1: memref<1000000xi32>, %arg2: memref<1000xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg2[%2] {handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.extui %0 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    memref.store %3, %arg0[%5] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<1000xi32>
    %6 = arith.cmpi ult, %c0_i32, %0 : i32
    cf.cond_br %6, ^bb2(%c0_i32 : i32), ^bb3
  ^bb2(%7: i32):  // 2 preds: ^bb1, ^bb2
    %8 = arith.extui %0 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    %10 = memref.load %arg0[%9] {handshake.name = "load2"} : memref<1000xi32>
    %11 = arith.extui %0 : i32 to i64
    %12 = arith.extui %7 : i32 to i64
    %c1000_i64 = arith.constant 1000 : i64
    %13 = arith.muli %11, %c1000_i64 : i64
    %14 = arith.addi %13, %12 : i64
    %15 = arith.index_cast %14 : i64 to index
    %16 = memref.load %arg1[%15] {handshake.name = "load3"} : memref<1000000xi32>
    %17 = arith.extui %7 : i32 to i64
    %18 = arith.index_cast %17 : i64 to index
    %19 = memref.load %arg0[%18] {handshake.name = "load4"} : memref<1000xi32>
    %20 = arith.muli %16, %19 : i32
    %21 = arith.subi %10, %20 : i32
    %22 = arith.extui %0 : i32 to i64
    %23 = arith.index_cast %22 : i64 to index
    memref.store %21, %arg0[%23] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<1000xi32>
    %24 = arith.addi %7, %c1_i32 : i32
    %25 = arith.cmpi ult, %24, %0 : i32
    cf.cond_br %25, ^bb2(%24 : i32), ^bb3
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %26 = arith.extui %0 : i32 to i64
    %27 = arith.index_cast %26 : i64 to index
    %28 = memref.load %arg0[%27] {handshake.name = "load6"} : memref<1000xi32>
    %29 = arith.extui %0 : i32 to i64
    %30 = arith.extui %0 : i32 to i64
    %c1000_i64_0 = arith.constant 1000 : i64
    %31 = arith.muli %29, %c1000_i64_0 : i64
    %32 = arith.addi %31, %30 : i64
    %33 = arith.index_cast %32 : i64 to index
    %34 = memref.load %arg1[%33] {handshake.name = "load7"} : memref<1000000xi32>
    %35 = arith.divsi %28, %34 : i32
    %36 = arith.extui %0 : i32 to i64
    %37 = arith.index_cast %36 : i64 to index
    memref.store %35, %arg0[%37] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store8"} : memref<1000xi32>
    %38 = arith.addi %0, %c1_i32 : i32
    %39 = arith.cmpi ult, %38, %c1000_i32 : i32
    cf.cond_br %39, ^bb1(%38 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
