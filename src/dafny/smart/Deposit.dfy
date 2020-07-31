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

module DepositTree {

    import opened Trees
    import opened MerkleTrees

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
        function method diff(a: int, b : int) : int 
    {
        a - b
    }

        function power2(n : nat): nat 
        ensures power2(n) >= 1
        ensures n >= 1 ==> power2(n) >= 2 

        decreases n
    {
        if n == 0 then 1 else 2 * power2(n - 1)
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
        var zerohashes: array<int>

        var deposit_count: int

        var branch: array<int>

        predicate Valid()
        reads this
            {
                deposit_count < power2(TREE_HEIGHT) - 1 &&
                branch.Length == TREE_HEIGHT == zerohashes.Length &&
                TREE_HEIGHT == height(root) 
            }

        method initializeZeroHashes()
        requires Valid()
        requires TREE_HEIGHT > 1
        modifies zerohashes
        requires zerohashes.Length == TREE_HEIGHT
        requires forall i :: 0 <= i < zerohashes.Length ==> zerohashes[i] == 0
        ensures Valid()
        ensures forall i :: 0 <= i < zerohashes.Length - 1 ==> zerohashes[i+1] == diff(zerohashes[i],zerohashes[i])
        {

            var x := 0;

            while x != TREE_HEIGHT - 1
                invariant 0 <= x < TREE_HEIGHT
                invariant forall i :: 0 <= i < x ==> zerohashes[i+1] == diff(zerohashes[i],zerohashes[i])
                invariant forall i :: x < i < zerohashes.Length ==> zerohashes[i] == 0
                decreases TREE_HEIGHT - x 
                {
                    zerohashes[x+1] := diff(zerohashes[x],zerohashes[x]);
                    x := x + 1;
                }

        }

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
                var size;
                while n != TREE_HEIGHT
                    invariant 0 <= n <= TREE_HEIGHT 
                    invariant deposit_count < power2(TREE_HEIGHT) 
                    decreases TREE_HEIGHT - n 
                    {
                        if deposit_count % 2 == 1 {
                            break;
                        }
                        value1 := diff(branch[n], value);
                        size := deposit_count / 2;
                        n := n + 1;
                    }
                    assert TREE_HEIGHT == branch.Length;
                    branch[n] := value;
            }

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
                    assert 
                    return r;
            }

} 
   


}
