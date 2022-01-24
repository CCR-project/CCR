/*-
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (c) 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 * Copyright (c) 2014 David T. Chisnall
 * All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Ronnie Kon at Mindcraft Inc., Kevin Lew and Elmer Yglesias.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <stddef.h>

/*
 * Build the list into a heap, where a heap is defined such that for
 * the records K1 ... KN, Kj/2 >= Kj for 1 <= j/2 <= j <= N.
 *
 * There two cases.  If j == nmemb, select largest of Ki and Kj.  If
 * j < nmemb, select largest of Ki, Kj and Kj+1.
 */
void create(int *base, size_t nmemb, size_t initval) {
  size_t par_i, child_i;
  int *par, *child;
  for (par_i = initval; (child_i = par_i * 2) <= nmemb; par_i = child_i) {
    child = base + child_i;
    if (child_i < nmemb && *child < *(child+1)) {
      ++child;
      ++child_i;
    }
    par = base + par_i;
    if (*child <= *par)
      break;
    int tmp = *par;
    *par = *child;
    *child = tmp;
  }
}

/*
 * Select the top of the heap and 'heapify'.  Since by far the most expensive
 * action is the call to the compar function, a considerable optimization
 * in the average case can be achieved due to the fact that k, the displaced
 * elememt, is usually quite small, so it would be preferable to first
 * heapify, always maintaining the invariant that the larger child is copied
 * over its parent's record.
 *
 * Then, starting from the *bottom* of the heap, finding k's correct place,
 * again maintianing the invariant.  As a result of the invariant no element
 * is 'lost' when k is assigned its correct place in the heap.
 *
 * The time savings from this optimization are on the order of 15-20% for the
 * average case. See Knuth, Vol. 3, page 158, problem 18.
 *
 * XXX Don't break the #define SELECT line, below.  Reiser cpp gets upset.
 */
void select_heapify(int *base, size_t nmemb, int k) {
  size_t par_i, child_i;
  int *par, *child;
  for (par_i = 1; (child_i = par_i * 2) <= nmemb; par_i = child_i) {
    child = base + child_i;
    if (child_i < nmemb && *child < *(child+1)) {
      ++child;
      ++child_i;
    }
    par = base + par_i;
    *par = *child;
  }
  for (;;) {
    child_i = par_i;
    par_i = child_i / 2;
    child = base + child_i;
    par = base + par_i;
    if (child_i == 1 || k < *par) {
      *child = k;
      break;
    }
    *child = *par;
  }
}

void heapsort(int *vbase, size_t nmemb) {
  if (nmemb <= 1)
    return;
  
  /*
   * Items are numbered from 1 to nmemb, so offset from size bytes
   * below the starting address.
   */
  int *base = vbase - 1;
  
  for (size_t l = nmemb / 2 + 1; --l;)
    create(base, nmemb, l);
  
  /*
   * For each element of the heap, save the largest element into its
   * final slot, save the displaced element (k), then recreate the
   * heap.
   */
  while (nmemb > 1) {
    int k = base[nmemb];
    base[nmemb] = base[1];
    --nmemb;
    select_heapify(base, nmemb, k);
  }
}
