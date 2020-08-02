/*
 * Copyright 2020 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

include "Trees.dfy"
include "MerkleTrees.dfy"
include "IntTree.dfy"
include "Helpers.dfy"

module DepositTree {

    import opened Trees
    import opened MerkleTrees
    import opened DiffTree
    import opened Helpers
    /** 
     *  Attribute hash.
     *
     */
    function hash<T>(a: T, b : T) : T 

    /**
     *  Check that a decorated tree correctly stores the diff attribute. 
     */
    predicate isDecoratedWithHash<T>(root: Tree<T>)
    {
        match root
            case Leaf(v, _, _) => true

            case Node(v, lc, rc, _, _) => v == hash(lc.v, rc.v)
    }
    /**
     *  Incremental algorithm.
     */
    class HashTree {

        /*
        * fun init() -> unit:
        *     i: int = 0
        *     while i < TREE_HEIGHT - 1:
        *         zerohashes[i+1] = hash(zerohashes[i], zerohashes[i])
        *         i += 1
        */

        ghost var root: Tree<int>
        const TREE_HEIGHT: nat
        var zerohashes: seq<int>
        var deposit_count: int

        var branch: array<int>

        constructor()
            ensures height(root) == TREE_HEIGHT
            ensures |zerohashes|== branch.Length == TREE_HEIGHT
            ensures isDecoratedWithDiff(root)
            ensures isCompleteTree(root)
            ensures root.v == getDiffOfNode(root)
            ensures zerohashes == initFun(TREE_HEIGHT, 0)


        predicate Valid()
        reads this
            {
                deposit_count < power2(TREE_HEIGHT) - 1 &&
                isCompleteTree(root) &&
                branch.Length == TREE_HEIGHT == |zerohashes| &&
                TREE_HEIGHT == height(root) && isDecoratedWithDiff(root) &&
                root.v == getDiffOfNode(root)
            }




        // method to initialize the branches array
        method initializeZeroHashes()
        requires Valid()
        requires TREE_HEIGHT > 1
        modifies branch
        requires branch.Length == TREE_HEIGHT
        requires forall i :: 0 <= i < branch.Length ==> branch[i] == 0
        ensures Valid()
        ensures forall i :: 0 <= i < branch.Length - 1 ==> branch[i+1] == diff(branch[i],branch[i])
        {

            var x := 0;

            while x != TREE_HEIGHT - 1
                invariant 0 <= x < TREE_HEIGHT
                invariant forall i :: 0 <= i < x ==> branch[i+1] == diff(branch[i],branch[i])
                invariant forall i :: x < i < branch.Length ==> branch[i] == 0
                decreases TREE_HEIGHT - x 
                {
                    branch[x+1] := diff(branch[x],branch[x]);
                    x := x + 1;
                }
                assert |zerohashes| == TREE_HEIGHT;
                assert branch.Length == TREE_HEIGHT;
                assert |zerohashes| == TREE_HEIGHT;
                var zh := castSeqToArray(zerohashes);
                assert zh.Length == |zerohashes|;
                assert zh == branch;

        }

        // Function to initiale the zerohashes array
        function initFun(length: nat, init: int): seq<int>
        ensures |initFun(length, init)| == length
        {
            if length == 0 then [] else [init] + initFun(length-1, diff(init,init))
        }

        method castSeqToArray(s:seq<int>) returns (a: array<int>)
            requires |s| != 0
            ensures |s| == a.Length
            {
                var i := 0;
                var seqLen := |s|;
                var arr := new int[seqLen];

                while i != |s|
                    invariant 0 <= i <= |s|
                    decreases |s| - i
                    {
                        arr[i] := s[i];
                        i := i + 1;
                    }
                    a := arr;
            }


        // Using this insertion algorithm allows branches[] to maintain a proof path of
        // the most recent insertion
        /*
        * fun deposit(value: int) -> unit:
        *     assert deposit_count < 2^TREE_HEIGHT - 1
        *     deposit_count += 1
        *     size: int = deposit_count
        *     i: int = 0
        *     while i < TREE_HEIGHT - 1:
        *         if size % 2 == 1:
        *             break
        *         value = hash(branch[i], value)
        *         size /= 2
        *         i += 1
        *     branch[i] = value
        */

        method deposit(value: int) returns (t: int)
            requires Valid()
            modifies this
            modifies branch
            ensures Valid()
            {

                var n := 0;
                deposit_count := deposit_count + 1;
                var value1 := value;
                var size := deposit_count;
                while n != TREE_HEIGHT
                    invariant 0 <= n <= TREE_HEIGHT 
                    invariant deposit_count < power2(TREE_HEIGHT) 
                    decreases TREE_HEIGHT - n 
                    {
                        if size % 2 == 1 {
                            break;
                        }
                        value1 := diff(branch[n], value);
                        size := size / 2;
                        n := n + 1;
                    }
                    assert TREE_HEIGHT == branch.Length;
                    branch[n] := value;
            }

        // We need a lemma to prove the n will not reach TREE_HEIGHT

        /*
        * fun __deposit_root() -> int:
        *     root: int = 0
        *     size: int = deposit_count
        *     h: int = 0
        *     while h < TREE_HEIGHT:
        *         if size % 2 == 1: # size is odd
        *             root = hash(branch[h], root)
        *         else:             # size is even
        *             root = hash(root, zerohashes[h])
        *         size /= 2
        *         h += 1
        *     return root
        */

        // once the deposit threshold is met
        // it calculates the root from branches[]
        method deposit_root() returns (r: int)
            requires Valid()
            ensures Valid()
            {
                
                var n := 0;
                var size := 0;
                while n != TREE_HEIGHT
                    invariant 0 <= n <= TREE_HEIGHT
                    decreases TREE_HEIGHT - n
                    {
                        if deposit_count % 2 == 1 {
                            r := diff(branch[n], r);
                        }else {
                            r := diff(r, zerohashes[n]);
                        }
                        size := size / 2;
                        n := n + 1;
                        
                    }
                    assert isDecoratedWithDiff(root);
                    assert r == getDiffOfNode(root);
                    assert r == root.v;
                    return r ;
            }

} 
   


}
