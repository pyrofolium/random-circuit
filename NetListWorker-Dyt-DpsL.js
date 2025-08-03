(function() {
  "use strict";
  function zip(a, b) {
    const length = Math.min(a.length, b.length);
    return Array.from({ length }, (_, i) => [a[i], b[i]]);
  }
  function colorFromString(randomString) {
    let hash = 0;
    for (let i = 0; i < randomString.length; i++) {
      hash = (hash << 5) - hash + randomString.charCodeAt(i);
      hash = hash & hash;
    }
    hash *= 1337;
    const r = Math.abs((hash & 16711680) >> 16);
    const g = Math.abs((hash & 65280) >> 8);
    const b = Math.abs(hash & 255);
    return `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${b.toString(16).padStart(2, "0")}`;
  }
  function createPinRenders(component, coord, width) {
    const topPadding = 1;
    const sidePadding = 0;
    const pins = component.pins;
    const leftPins = pins.slice(0, pins.length / 2);
    const rightPins = pins.slice(pins.length / 2, pins.length);
    const leftPinRenders = leftPins.map((pin, index) => {
      return {
        pin,
        coord: {
          x: coord.x + sidePadding,
          y: coord.y + index + topPadding
        },
        leftOrRight: "left"
      };
    });
    const rightPinRenders = rightPins.map((pin, index) => {
      return {
        pin,
        coord: {
          x: coord.x + width - sidePadding,
          y: coord.y + index + topPadding
        },
        leftOrRight: "right"
      };
    });
    return leftPinRenders.concat(rightPinRenders);
  }
  function calculateComponentDimensions(component) {
    const internalPadding = 1;
    const nameLength = component.name.length;
    const longestPinNameLength = Math.max(...component.pins.map(({ name }) => name.length));
    let width = Math.floor((longestPinNameLength * 2 + nameLength) / 1.5) + internalPadding;
    let height = Math.ceil(component.pins.length / 2) + internalPadding;
    width = width % 2 !== 0 ? width - 1 : width;
    height = height % 2 !== 0 ? height : height;
    return [width, height];
  }
  function calculateAllComponentDimensions(optimizedNetList) {
    return Object.entries(
      optimizedNetList.components
    ).map(([, component]) => calculateComponentDimensions(component));
  }
  function createComponentRender(component, coord, width, height) {
    const pinRenders = createPinRenders(component, coord, width);
    return {
      component,
      coord,
      width,
      height,
      pinRenders
    };
  }
  function createAllComponentRenders(componentPositions, optimizedNetList, componentDimensions) {
    const components = Object.entries(optimizedNetList.components).map(([, component]) => component);
    const groupedComponentData = zip(
      componentPositions,
      zip(components, componentDimensions)
    );
    return groupedComponentData.map(([coord, [component, [width, height]]]) => createComponentRender(component, coord, width, height));
  }
  const BIAS_AGAINST_CROSSING_A_WIRE = 999;
  var minPriorityQueue = {};
  var heap$1 = {};
  var heap = {};
  /**
   * @license MIT
   * @copyright 2020 Eyas Ranjous <eyas.ranjous@gmail.com>
   *
   * @class
   */
  var hasRequiredHeap$1;
  function requireHeap$1() {
    if (hasRequiredHeap$1) return heap;
    hasRequiredHeap$1 = 1;
    class Heap {
      /**
       * @param {function} compare
       * @param {array} [_values]
       * @param {number|string|object} [_leaf]
       */
      constructor(compare, _values, _leaf) {
        if (typeof compare !== "function") {
          throw new Error("Heap constructor expects a compare function");
        }
        this._compare = compare;
        this._nodes = Array.isArray(_values) ? _values : [];
        this._leaf = _leaf || null;
      }
      /**
       * Converts the heap to a cloned array without sorting.
       * @public
       * @returns {Array}
       */
      toArray() {
        return Array.from(this._nodes);
      }
      /**
       * Checks if a parent has a left child
       * @private
       */
      _hasLeftChild(parentIndex) {
        const leftChildIndex = parentIndex * 2 + 1;
        return leftChildIndex < this.size();
      }
      /**
       * Checks if a parent has a right child
       * @private
       */
      _hasRightChild(parentIndex) {
        const rightChildIndex = parentIndex * 2 + 2;
        return rightChildIndex < this.size();
      }
      /**
       * Compares two nodes
       * @private
       */
      _compareAt(i, j) {
        return this._compare(this._nodes[i], this._nodes[j]);
      }
      /**
       * Swaps two nodes in the heap
       * @private
       */
      _swap(i, j) {
        const temp = this._nodes[i];
        this._nodes[i] = this._nodes[j];
        this._nodes[j] = temp;
      }
      /**
       * Checks if parent and child should be swapped
       * @private
       */
      _shouldSwap(parentIndex, childIndex) {
        if (parentIndex < 0 || parentIndex >= this.size()) {
          return false;
        }
        if (childIndex < 0 || childIndex >= this.size()) {
          return false;
        }
        return this._compareAt(parentIndex, childIndex) > 0;
      }
      /**
       * Compares children of a parent
       * @private
       */
      _compareChildrenOf(parentIndex) {
        if (!this._hasLeftChild(parentIndex) && !this._hasRightChild(parentIndex)) {
          return -1;
        }
        const leftChildIndex = parentIndex * 2 + 1;
        const rightChildIndex = parentIndex * 2 + 2;
        if (!this._hasLeftChild(parentIndex)) {
          return rightChildIndex;
        }
        if (!this._hasRightChild(parentIndex)) {
          return leftChildIndex;
        }
        const compare = this._compareAt(leftChildIndex, rightChildIndex);
        return compare > 0 ? rightChildIndex : leftChildIndex;
      }
      /**
       * Compares two children before a position
       * @private
       */
      _compareChildrenBefore(index, leftChildIndex, rightChildIndex) {
        const compare = this._compareAt(rightChildIndex, leftChildIndex);
        if (compare <= 0 && rightChildIndex < index) {
          return rightChildIndex;
        }
        return leftChildIndex;
      }
      /**
       * Recursively bubbles up a node if it's in a wrong position
       * @private
       */
      _heapifyUp(startIndex) {
        let childIndex = startIndex;
        let parentIndex = Math.floor((childIndex - 1) / 2);
        while (this._shouldSwap(parentIndex, childIndex)) {
          this._swap(parentIndex, childIndex);
          childIndex = parentIndex;
          parentIndex = Math.floor((childIndex - 1) / 2);
        }
      }
      /**
       * Recursively bubbles down a node if it's in a wrong position
       * @private
       */
      _heapifyDown(startIndex) {
        let parentIndex = startIndex;
        let childIndex = this._compareChildrenOf(parentIndex);
        while (this._shouldSwap(parentIndex, childIndex)) {
          this._swap(parentIndex, childIndex);
          parentIndex = childIndex;
          childIndex = this._compareChildrenOf(parentIndex);
        }
      }
      /**
       * Recursively bubbles down a node before a given index
       * @private
       */
      _heapifyDownUntil(index) {
        let parentIndex = 0;
        let leftChildIndex = 1;
        let rightChildIndex = 2;
        let childIndex;
        while (leftChildIndex < index) {
          childIndex = this._compareChildrenBefore(
            index,
            leftChildIndex,
            rightChildIndex
          );
          if (this._shouldSwap(parentIndex, childIndex)) {
            this._swap(parentIndex, childIndex);
          }
          parentIndex = childIndex;
          leftChildIndex = parentIndex * 2 + 1;
          rightChildIndex = parentIndex * 2 + 2;
        }
      }
      /**
       * Inserts a new value into the heap
       * @public
       * @param {number|string|object} value
       * @returns {Heap}
       */
      insert(value) {
        this._nodes.push(value);
        this._heapifyUp(this.size() - 1);
        if (this._leaf === null || this._compare(value, this._leaf) > 0) {
          this._leaf = value;
        }
        return this;
      }
      /**
       * Inserts a new value into the heap
       * @public
       * @param {number|string|object} value
       * @returns {Heap}
       */
      push(value) {
        return this.insert(value);
      }
      /**
       * Removes and returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      extractRoot() {
        if (this.isEmpty()) {
          return null;
        }
        const root = this.root();
        this._nodes[0] = this._nodes[this.size() - 1];
        this._nodes.pop();
        this._heapifyDown(0);
        if (root === this._leaf) {
          this._leaf = this.root();
        }
        return root;
      }
      /**
       * Removes and returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      pop() {
        return this.extractRoot();
      }
      /**
       * Applies heap sort and return the values sorted by priority
       * @public
       * @returns {array}
       */
      sort() {
        for (let i = this.size() - 1; i > 0; i -= 1) {
          this._swap(0, i);
          this._heapifyDownUntil(i);
        }
        return this._nodes;
      }
      /**
       * Fixes node positions in the heap
       * @public
       * @returns {Heap}
       */
      fix() {
        for (let i = Math.floor(this.size() / 2) - 1; i >= 0; i -= 1) {
          this._heapifyDown(i);
        }
        for (let i = Math.floor(this.size() / 2); i < this.size(); i += 1) {
          const value = this._nodes[i];
          if (this._leaf === null || this._compare(value, this._leaf) > 0) {
            this._leaf = value;
          }
        }
        return this;
      }
      /**
       * Verifies that all heap nodes are in the right position
       * @public
       * @returns {boolean}
       */
      isValid() {
        const isValidRecursive = (parentIndex) => {
          let isValidLeft = true;
          let isValidRight = true;
          if (this._hasLeftChild(parentIndex)) {
            const leftChildIndex = parentIndex * 2 + 1;
            if (this._compareAt(parentIndex, leftChildIndex) > 0) {
              return false;
            }
            isValidLeft = isValidRecursive(leftChildIndex);
          }
          if (this._hasRightChild(parentIndex)) {
            const rightChildIndex = parentIndex * 2 + 2;
            if (this._compareAt(parentIndex, rightChildIndex) > 0) {
              return false;
            }
            isValidRight = isValidRecursive(rightChildIndex);
          }
          return isValidLeft && isValidRight;
        };
        return isValidRecursive(0);
      }
      /**
       * Returns a shallow copy of the heap
       * @public
       * @returns {Heap}
       */
      clone() {
        return new Heap(this._compare, this._nodes.slice(), this._leaf);
      }
      /**
       * Returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      root() {
        if (this.isEmpty()) {
          return null;
        }
        return this._nodes[0];
      }
      /**
       * Returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      top() {
        return this.root();
      }
      /**
       * Returns a leaf node in the heap
       * @public
       * @returns {number|string|object}
       */
      leaf() {
        return this._leaf;
      }
      /**
       * Returns the number of nodes in the heap
       * @public
       * @returns {number}
       */
      size() {
        return this._nodes.length;
      }
      /**
       * Checks if the heap is empty
       * @public
       * @returns {boolean}
       */
      isEmpty() {
        return this.size() === 0;
      }
      /**
       * Clears the heap
       * @public
       */
      clear() {
        this._nodes = [];
        this._leaf = null;
      }
      /**
       * Implements an iterable on the heap
       * @public
       */
      [Symbol.iterator]() {
        let size = this.size();
        return {
          next: () => {
            size -= 1;
            return {
              value: this.pop(),
              done: size === -1
            };
          }
        };
      }
      /**
       * Builds a heap from a array of values
       * @public
       * @static
       * @param {array} values
       * @param {function} compare
       * @returns {Heap}
       */
      static heapify(values, compare) {
        if (!Array.isArray(values)) {
          throw new Error("Heap.heapify expects an array of values");
        }
        if (typeof compare !== "function") {
          throw new Error("Heap.heapify expects a compare function");
        }
        return new Heap(compare, values).fix();
      }
      /**
       * Checks if a list of values is a valid heap
       * @public
       * @static
       * @param {array} values
       * @param {function} compare
       * @returns {boolean}
       */
      static isHeapified(values, compare) {
        return new Heap(compare, values).isValid();
      }
    }
    heap.Heap = Heap;
    return heap;
  }
  var minHeap = {};
  /**
   * @license MIT
   * @copyright 2020 Eyas Ranjous <eyas.ranjous@gmail.com>
   */
  var hasRequiredMinHeap;
  function requireMinHeap() {
    if (hasRequiredMinHeap) return minHeap;
    hasRequiredMinHeap = 1;
    const { Heap } = requireHeap$1();
    const getMinCompare = (getCompareValue) => (a, b) => {
      const aVal = typeof getCompareValue === "function" ? getCompareValue(a) : a;
      const bVal = typeof getCompareValue === "function" ? getCompareValue(b) : b;
      return aVal <= bVal ? -1 : 1;
    };
    class MinHeap {
      /**
       * @param {function} [getCompareValue]
       * @param {Heap} [_heap]
       */
      constructor(getCompareValue, _heap) {
        this._getCompareValue = getCompareValue;
        this._heap = _heap || new Heap(getMinCompare(getCompareValue));
      }
      /**
       * Converts the heap to a cloned array without sorting.
       * @public
       * @returns {Array}
       */
      toArray() {
        return Array.from(this._heap._nodes);
      }
      /**
       * Inserts a new value into the heap
       * @public
       * @param {number|string|object} value
       * @returns {MinHeap}
       */
      insert(value) {
        return this._heap.insert(value);
      }
      /**
       * Inserts a new value into the heap
       * @public
       * @param {number|string|object} value
       * @returns {Heap}
       */
      push(value) {
        return this.insert(value);
      }
      /**
       * Removes and returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      extractRoot() {
        return this._heap.extractRoot();
      }
      /**
       * Removes and returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      pop() {
        return this.extractRoot();
      }
      /**
       * Applies heap sort and return the values sorted by priority
       * @public
       * @returns {array}
       */
      sort() {
        return this._heap.sort();
      }
      /**
       * Fixes node positions in the heap
       * @public
       * @returns {MinHeap}
       */
      fix() {
        return this._heap.fix();
      }
      /**
       * Verifies that all heap nodes are in the right position
       * @public
       * @returns {boolean}
       */
      isValid() {
        return this._heap.isValid();
      }
      /**
       * Returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      root() {
        return this._heap.root();
      }
      /**
       * Returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      top() {
        return this.root();
      }
      /**
       * Returns a leaf node in the heap
       * @public
       * @returns {number|string|object}
       */
      leaf() {
        return this._heap.leaf();
      }
      /**
       * Returns the number of nodes in the heap
       * @public
       * @returns {number}
       */
      size() {
        return this._heap.size();
      }
      /**
       * Checks if the heap is empty
       * @public
       * @returns {boolean}
       */
      isEmpty() {
        return this._heap.isEmpty();
      }
      /**
       * Clears the heap
       * @public
       */
      clear() {
        this._heap.clear();
      }
      /**
       * Returns a shallow copy of the MinHeap
       * @public
       * @returns {MinHeap}
       */
      clone() {
        return new MinHeap(this._getCompareValue, this._heap.clone());
      }
      /**
       * Implements an iterable on the heap
       * @public
       */
      [Symbol.iterator]() {
        let size = this.size();
        return {
          next: () => {
            size -= 1;
            return {
              value: this.pop(),
              done: size === -1
            };
          }
        };
      }
      /**
       * Builds a MinHeap from an array
       * @public
       * @static
       * @param {array} values
       * @param {function} [getCompareValue]
       * @returns {MinHeap}
       */
      static heapify(values, getCompareValue) {
        if (!Array.isArray(values)) {
          throw new Error("MinHeap.heapify expects an array");
        }
        const heap2 = new Heap(getMinCompare(getCompareValue), values);
        return new MinHeap(getCompareValue, heap2).fix();
      }
      /**
       * Checks if a list of values is a valid min heap
       * @public
       * @static
       * @param {array} values
       * @param {function} [getCompareValue]
       * @returns {boolean}
       */
      static isHeapified(values, getCompareValue) {
        const heap2 = new Heap(getMinCompare(getCompareValue), values);
        return new MinHeap(getCompareValue, heap2).isValid();
      }
    }
    minHeap.MinHeap = MinHeap;
    return minHeap;
  }
  var maxHeap = {};
  /**
   * @license MIT
   * @copyright 2020 Eyas Ranjous <eyas.ranjous@gmail.com>
   */
  var hasRequiredMaxHeap;
  function requireMaxHeap() {
    if (hasRequiredMaxHeap) return maxHeap;
    hasRequiredMaxHeap = 1;
    const { Heap } = requireHeap$1();
    const getMaxCompare = (getCompareValue) => (a, b) => {
      const aVal = typeof getCompareValue === "function" ? getCompareValue(a) : a;
      const bVal = typeof getCompareValue === "function" ? getCompareValue(b) : b;
      return aVal < bVal ? 1 : -1;
    };
    class MaxHeap {
      /**
       * @param {function} [getCompareValue]
       * @param {Heap} [_heap]
       */
      constructor(getCompareValue, _heap) {
        this._getCompareValue = getCompareValue;
        this._heap = _heap || new Heap(getMaxCompare(getCompareValue));
      }
      /**
       * Inserts a new value into the heap
       * @public
       * @param {number|string|object} value
       * @returns {MaxHeap}
       */
      insert(value) {
        return this._heap.insert(value);
      }
      /**
       * Inserts a new value into the heap
       * @public
       * @param {number|string|object} value
       * @returns {Heap}
       */
      push(value) {
        return this.insert(value);
      }
      /**
       * Removes and returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      extractRoot() {
        return this._heap.extractRoot();
      }
      /**
       * Removes and returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      pop() {
        return this.extractRoot();
      }
      /**
       * Applies heap sort and return the values sorted by priority
       * @public
       * @returns {array}
       */
      sort() {
        return this._heap.sort();
      }
      /**
       * Converts the heap to a cloned array without sorting.
       * @public
       * @returns {Array}
       */
      toArray() {
        return Array.from(this._heap._nodes);
      }
      /**
       * Fixes node positions in the heap
       * @public
       * @returns {MaxHeap}
       */
      fix() {
        return this._heap.fix();
      }
      /**
       * Verifies that all heap nodes are in the right position
       * @public
       * @returns {boolean}
       */
      isValid() {
        return this._heap.isValid();
      }
      /**
       * Returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      root() {
        return this._heap.root();
      }
      /**
       * Returns the root node in the heap
       * @public
       * @returns {number|string|object}
       */
      top() {
        return this.root();
      }
      /**
       * Returns a leaf node in the heap
       * @public
       * @returns {number|string|object}
       */
      leaf() {
        return this._heap.leaf();
      }
      /**
       * Returns the number of nodes in the heap
       * @public
       * @returns {number}
       */
      size() {
        return this._heap.size();
      }
      /**
       * Checks if the heap is empty
       * @public
       * @returns {boolean}
       */
      isEmpty() {
        return this._heap.isEmpty();
      }
      /**
       * Clears the heap
       * @public
       */
      clear() {
        this._heap.clear();
      }
      /**
       * Returns a shallow copy of the MaxHeap
       * @public
       * @returns {MaxHeap}
       */
      clone() {
        return new MaxHeap(this._getCompareValue, this._heap.clone());
      }
      /**
       * Implements an iterable on the heap
       * @public
       */
      [Symbol.iterator]() {
        let size = this.size();
        return {
          next: () => {
            size -= 1;
            return {
              value: this.pop(),
              done: size === -1
            };
          }
        };
      }
      /**
       * Builds a MaxHeap from an array
       * @public
       * @static
       * @param {array} values
       * @param {function} [getCompareValue]
       * @returns {MaxHeap}
       */
      static heapify(values, getCompareValue) {
        if (!Array.isArray(values)) {
          throw new Error("MaxHeap.heapify expects an array");
        }
        const heap2 = new Heap(getMaxCompare(getCompareValue), values);
        return new MaxHeap(getCompareValue, heap2).fix();
      }
      /**
       * Checks if a list of values is a valid max heap
       * @public
       * @static
       * @param {array} values
       * @param {function} [getCompareValue]
       * @returns {boolean}
       */
      static isHeapified(values, getCompareValue) {
        const heap2 = new Heap(getMaxCompare(getCompareValue), values);
        return new MaxHeap(getCompareValue, heap2).isValid();
      }
    }
    maxHeap.MaxHeap = MaxHeap;
    return maxHeap;
  }
  var hasRequiredHeap;
  function requireHeap() {
    if (hasRequiredHeap) return heap$1;
    hasRequiredHeap = 1;
    const { Heap } = requireHeap$1();
    const { MinHeap } = requireMinHeap();
    const { MaxHeap } = requireMaxHeap();
    heap$1.Heap = Heap;
    heap$1.MinHeap = MinHeap;
    heap$1.MaxHeap = MaxHeap;
    return heap$1;
  }
  /**
   * @copyright 2020 Eyas Ranjous <eyas.ranjous@gmail.com>
   * @license MIT
   */
  var hasRequiredMinPriorityQueue;
  function requireMinPriorityQueue() {
    if (hasRequiredMinPriorityQueue) return minPriorityQueue;
    hasRequiredMinPriorityQueue = 1;
    const { Heap, MinHeap } = requireHeap();
    const getMinCompare = (getCompareValue) => (a, b) => {
      const aVal = typeof getCompareValue === "function" ? getCompareValue(a) : a;
      const bVal = typeof getCompareValue === "function" ? getCompareValue(b) : b;
      return aVal <= bVal ? -1 : 1;
    };
    class MinPriorityQueue {
      constructor(options, _heap) {
        if (options && typeof options === "object" && typeof options.compare === "function") {
          this._getCompareValue = null;
          const compareFunction = (a, b) => options.compare(a, b) <= 0 ? -1 : 1;
          this._heap = _heap || new Heap(compareFunction);
        } else {
          const getCompareValue = options;
          if (getCompareValue && typeof getCompareValue !== "function") {
            throw new Error("MinPriorityQueue constructor requires a callback for object values");
          }
          this._heap = _heap || new MinHeap(getCompareValue);
        }
      }
      /**
       * Returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      front() {
        return this._heap.root();
      }
      /**
       * Returns an element with lowest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      back() {
        return this._heap.leaf();
      }
      /**
       * Adds a value to the queue
       * @public
       * @param {number|string|object} value
       * @returns {MinPriorityQueue}
       */
      enqueue(value) {
        return this._heap.insert(value);
      }
      /**
       * Adds a value to the queue
       * @public
       * @param {number|string|object} value
       * @returns {MinPriorityQueue}
       */
      push(value) {
        return this.enqueue(value);
      }
      /**
       * Removes and returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      dequeue() {
        return this._heap.extractRoot();
      }
      /**
       * Removes and returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      pop() {
        return this.dequeue();
      }
      /**
       * Removes all elements that match a criteria in the callback
       * @public
       * @param {function} cb
       * @returns {array}
       */
      remove(cb) {
        if (typeof cb !== "function") {
          throw new Error("MinPriorityQueue remove expects a callback");
        }
        const removed = [];
        const dequeued = [];
        while (!this.isEmpty()) {
          const popped = this.pop();
          if (cb(popped)) {
            removed.push(popped);
          } else {
            dequeued.push(popped);
          }
        }
        dequeued.forEach((val) => this.push(val));
        return removed;
      }
      /**
       * Checks if the queue contains an element that matches a criteria
       * @public
       * @param {function} cb
       * @returns {boolean}
       */
      contains(cb) {
        if (typeof cb !== "function") {
          throw new Error("MinPriorityQueue contains expects a callback");
        }
        let found = false;
        const dequeued = [];
        while (!this.isEmpty()) {
          const popped = this.pop();
          dequeued.push(popped);
          if (cb(popped)) {
            found = true;
            break;
          }
        }
        dequeued.forEach((val) => this.push(val));
        return found;
      }
      /**
       * Returns the number of elements in the queue
       * @public
       * @returns {number}
       */
      size() {
        return this._heap.size();
      }
      /**
       * Checks if the queue is empty
       * @public
       * @returns {boolean}
       */
      isEmpty() {
        return this._heap.isEmpty();
      }
      /**
       * Clears the queue
       * @public
       */
      clear() {
        this._heap.clear();
      }
      /**
       * Returns a sorted list of elements from highest to lowest priority
       * @public
       * @returns {array}
       */
      toArray() {
        return this._heap.clone().sort().reverse();
      }
      /**
       * Implements an iterable on the min priority queue
       * @public
       */
      [Symbol.iterator]() {
        let size = this.size();
        return {
          next: () => {
            size -= 1;
            return {
              value: this.pop(),
              done: size === -1
            };
          }
        };
      }
      /**
       * Creates a priority queue from an existing array
       * @public
       * @static
       * @returns {MinPriorityQueue}
       */
      static fromArray(values, getCompareValue) {
        const heap2 = new Heap(getMinCompare(getCompareValue), values);
        return new MinPriorityQueue(
          getCompareValue,
          new MinHeap(getCompareValue, heap2).fix()
        );
      }
    }
    minPriorityQueue.MinPriorityQueue = MinPriorityQueue;
    return minPriorityQueue;
  }
  var maxPriorityQueue = {};
  /**
   * @copyright 2020 Eyas Ranjous <eyas.ranjous@gmail.com>
   * @license MIT
   */
  var hasRequiredMaxPriorityQueue;
  function requireMaxPriorityQueue() {
    if (hasRequiredMaxPriorityQueue) return maxPriorityQueue;
    hasRequiredMaxPriorityQueue = 1;
    const { Heap, MaxHeap } = requireHeap();
    const getMaxCompare = (getCompareValue) => (a, b) => {
      const aVal = typeof getCompareValue === "function" ? getCompareValue(a) : a;
      const bVal = typeof getCompareValue === "function" ? getCompareValue(b) : b;
      return aVal < bVal ? 1 : -1;
    };
    class MaxPriorityQueue {
      constructor(options, _heap) {
        if (options && typeof options === "object" && typeof options.compare === "function") {
          this._getCompareValue = null;
          const compareFunction = (a, b) => options.compare(a, b) >= 0 ? -1 : 1;
          this._heap = _heap || new Heap(compareFunction);
        } else {
          const getCompareValue = options;
          if (getCompareValue && typeof getCompareValue !== "function") {
            throw new Error("MaxPriorityQueue constructor requires a callback for object values");
          }
          this._heap = _heap || new MaxHeap(getCompareValue);
        }
      }
      /**
       * Returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      front() {
        return this._heap.root();
      }
      /**
       * Returns an element with lowest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      back() {
        return this._heap.leaf();
      }
      /**
       * Adds a value to the queue
       * @public
       * @param {number|string|object} value
       * @returns {MaxPriorityQueue}
       */
      enqueue(value) {
        return this._heap.insert(value);
      }
      /**
       * Adds a value to the queue
       * @public
       * @param {number|string|object} value
       * @returns {MaxPriorityQueue}
       */
      push(value) {
        return this.enqueue(value);
      }
      /**
       * Removes and returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      dequeue() {
        return this._heap.extractRoot();
      }
      /**
       * Removes and returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      pop() {
        return this.dequeue();
      }
      /**
       * Removes all elements that match a criteria in the callback
       * @public
       * @param {function} cb
       * @returns {array}
       */
      remove(cb) {
        if (typeof cb !== "function") {
          throw new Error("MaxPriorityQueue remove expects a callback");
        }
        const removed = [];
        const dequeued = [];
        while (!this.isEmpty()) {
          const popped = this.pop();
          if (cb(popped)) {
            removed.push(popped);
          } else {
            dequeued.push(popped);
          }
        }
        dequeued.forEach((val) => this.push(val));
        return removed;
      }
      /**
       * Checks if the queue contains an element that matches a criteria
       * @public
       * @param {function} cb
       * @returns {boolean}
       */
      contains(cb) {
        if (typeof cb !== "function") {
          throw new Error("MaxPriorityQueue contains expects a callback");
        }
        let found = false;
        const dequeued = [];
        while (!this.isEmpty()) {
          const popped = this.pop();
          dequeued.push(popped);
          if (cb(popped)) {
            found = true;
            break;
          }
        }
        dequeued.forEach((val) => this.push(val));
        return found;
      }
      /**
       * Returns the number of elements in the queue
       * @public
       * @returns {number}
       */
      size() {
        return this._heap.size();
      }
      /**
       * Checks if the queue is empty
       * @public
       * @returns {boolean}
       */
      isEmpty() {
        return this._heap.isEmpty();
      }
      /**
       * Clears the queue
       * @public
       */
      clear() {
        this._heap.clear();
      }
      /**
       * Returns a sorted list of elements from highest to lowest priority
       * @public
       * @returns {array}
       */
      toArray() {
        return this._heap.clone().sort().reverse();
      }
      /**
       * Implements an iterable on the min priority queue
       * @public
       */
      [Symbol.iterator]() {
        let size = this.size();
        return {
          next: () => {
            size -= 1;
            return {
              value: this.pop(),
              done: size === -1
            };
          }
        };
      }
      /**
       * Creates a priority queue from an existing array
       * @public
       * @static
       * @returns {MaxPriorityQueue}
       */
      static fromArray(values, getCompareValue) {
        const heap2 = new Heap(getMaxCompare(getCompareValue), values);
        return new MaxPriorityQueue(
          getCompareValue,
          new MaxHeap(getCompareValue, heap2).fix()
        );
      }
    }
    maxPriorityQueue.MaxPriorityQueue = MaxPriorityQueue;
    return maxPriorityQueue;
  }
  var priorityQueue$1 = {};
  /**
   * @copyright 2020 Eyas Ranjous <eyas.ranjous@gmail.com>
   * @license MIT
   */
  var hasRequiredPriorityQueue$1;
  function requirePriorityQueue$1() {
    if (hasRequiredPriorityQueue$1) return priorityQueue$1;
    hasRequiredPriorityQueue$1 = 1;
    const { Heap } = requireHeap();
    class PriorityQueue {
      /**
       * Creates a priority queue
       * @params {function} compare
       */
      constructor(compare, _values) {
        if (typeof compare !== "function") {
          throw new Error("PriorityQueue constructor expects a compare function");
        }
        this._heap = new Heap(compare, _values);
        if (_values) {
          this._heap.fix();
        }
      }
      /**
       * Returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      front() {
        return this._heap.root();
      }
      /**
       * Returns an element with lowest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      back() {
        return this._heap.leaf();
      }
      /**
       * Adds a value to the queue
       * @public
       * @param {number|string|object} value
       * @returns {PriorityQueue}
       */
      enqueue(value) {
        return this._heap.insert(value);
      }
      /**
       * Adds a value to the queue
       * @public
       * @param {number|string|object} value
       * @returns {PriorityQueue}
       */
      push(value) {
        return this.enqueue(value);
      }
      /**
       * Removes and returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      dequeue() {
        return this._heap.extractRoot();
      }
      /**
       * Removes and returns an element with highest priority in the queue
       * @public
       * @returns {number|string|object}
       */
      pop() {
        return this.dequeue();
      }
      /**
       * Removes all elements that match a criteria in the callback
       * @public
       * @param {function} cb
       * @returns {array}
       */
      remove(cb) {
        if (typeof cb !== "function") {
          throw new Error("PriorityQueue remove expects a callback");
        }
        const removed = [];
        const dequeued = [];
        while (!this.isEmpty()) {
          const popped = this.pop();
          if (cb(popped)) {
            removed.push(popped);
          } else {
            dequeued.push(popped);
          }
        }
        dequeued.forEach((val) => this.push(val));
        return removed;
      }
      /**
       * Checks if the queue contains an element that matches a criteria
       * @public
       * @param {function} cb
       * @returns {boolean}
       */
      contains(cb) {
        if (typeof cb !== "function") {
          throw new Error("PriorityQueue contains expects a callback");
        }
        let found = false;
        const dequeued = [];
        while (!this.isEmpty()) {
          const popped = this.pop();
          dequeued.push(popped);
          if (cb(popped)) {
            found = true;
            break;
          }
        }
        dequeued.forEach((val) => this.push(val));
        return found;
      }
      /**
       * Returns the number of elements in the queue
       * @public
       * @returns {number}
       */
      size() {
        return this._heap.size();
      }
      /**
       * Checks if the queue is empty
       * @public
       * @returns {boolean}
       */
      isEmpty() {
        return this._heap.isEmpty();
      }
      /**
       * Clears the queue
       * @public
       */
      clear() {
        this._heap.clear();
      }
      /**
       * Returns a sorted list of elements from highest to lowest priority
       * @public
       * @returns {array}
       */
      toArray() {
        return this._heap.clone().sort().reverse();
      }
      /**
       * Implements an iterable on the priority queue
       * @public
       */
      [Symbol.iterator]() {
        let size = this.size();
        return {
          next: () => {
            size -= 1;
            return {
              value: this.pop(),
              done: size === -1
            };
          }
        };
      }
      /**
       * Creates a priority queue from an existing array
       * @public
       * @static
       * @returns {PriorityQueue}
       */
      static fromArray(values, compare) {
        return new PriorityQueue(compare, values);
      }
    }
    priorityQueue$1.PriorityQueue = PriorityQueue;
    return priorityQueue$1;
  }
  var priorityQueue;
  var hasRequiredPriorityQueue;
  function requirePriorityQueue() {
    if (hasRequiredPriorityQueue) return priorityQueue;
    hasRequiredPriorityQueue = 1;
    const { MinPriorityQueue } = requireMinPriorityQueue();
    const { MaxPriorityQueue } = requireMaxPriorityQueue();
    const { PriorityQueue } = requirePriorityQueue$1();
    priorityQueue = { MinPriorityQueue, MaxPriorityQueue, PriorityQueue };
    return priorityQueue;
  }
  var priorityQueueExports = requirePriorityQueue();
  function generateGrid(sideLength, defaultValue) {
    const acc = [];
    for (let y = 0; y < sideLength; y++) {
      const row = [];
      for (let x = 0; x < sideLength; x++) {
        row.push(defaultValue);
      }
      acc.push(row);
    }
    return acc;
  }
  function getSurroundingCoord(coord, gridSideLength, traversedGrid) {
    return [
      {
        x: coord.x - 1,
        y: coord.y - 1
      },
      {
        x: coord.x,
        y: coord.y - 1
      },
      {
        x: coord.x + 1,
        y: coord.y - 1
      },
      {
        x: coord.x + 1,
        y: coord.y
      },
      {
        x: coord.x + 1,
        y: coord.y + 1
      },
      {
        x: coord.x,
        y: coord.y + 1
      },
      {
        x: coord.x - 1,
        y: coord.y + 1
      },
      {
        x: coord.x - 1,
        y: coord.y
      }
    ].map((coord2, index) => [index % 2 === 0, coord2]).filter(
      ([, { x, y }]) => x >= 0 && y >= 0 && x < gridSideLength && y < gridSideLength && !traversedGrid[y][x]
    );
  }
  function getProjectedPoint(coordLinkList) {
    const a = coordLinkList.cameFrom?.coord;
    const b = coordLinkList.coord;
    if (a === void 0) {
      return void 0;
    }
    if (a.x === b.x) {
      const dy2 = b.y - a.y;
      return {
        x: b.x,
        y: b.y + dy2
      };
    }
    if (a.y === b.y) {
      const dx2 = b.x - a.x;
      return {
        x: b.x + dx2,
        y: b.y
      };
    }
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    return {
      x: b.x + dx,
      y: b.y + dy
    };
  }
  function isNewCoordATurn(coord, coordLinkedList) {
    const projectedCoord = getProjectedPoint(coordLinkedList);
    if (projectedCoord === void 0) {
      return false;
    }
    return !(projectedCoord.x === coord.x && projectedCoord.y === coord.y);
  }
  function coordLinkedListToArray(coordLinkedList) {
    if (coordLinkedList.cameFrom === void 0) {
      return [coordLinkedList.coord];
    } else {
      return [coordLinkedList.coord].concat(coordLinkedListToArray(coordLinkedList.cameFrom));
    }
  }
  function findShortestPath(costGrid, start, end) {
    const traversedGrid = generateGrid(costGrid.length, false);
    const turnCoordIntoKey = ({ x, y }) => x.toString() + "," + y.toString();
    const keyedEndCoords = new Set(end.map(turnCoordIntoKey));
    const isCoordGoalReached = (coord) => keyedEndCoords.has(turnCoordIntoKey(coord));
    const isCoordTraversed = ({ x, y }) => traversedGrid[y][x];
    const queue = new priorityQueueExports.MinPriorityQueue(
      ({ currentCost }) => currentCost
    );
    queue.enqueue({ coord: start, currentCost: 0, cameFrom: void 0 });
    let currentCoord;
    while (!queue.isEmpty()) {
      currentCoord = queue.pop();
      if (currentCoord === null) {
        throw Error("popped empty queue, error");
      }
      if (isCoordTraversed(currentCoord.coord)) {
        continue;
      }
      if (isCoordGoalReached(currentCoord.coord)) {
        break;
      }
      if (!Number.isFinite(currentCoord.currentCost)) {
        continue;
      }
      traversedGrid[currentCoord.coord.y][currentCoord.coord.x] = true;
      const surroundingCoords = getSurroundingCoord(currentCoord.coord, costGrid.length, traversedGrid);
      for (const [isDiagonalMove, coord] of surroundingCoords) {
        const costOfMove = isDiagonalMove ? 3 : 2;
        const isTurn = isNewCoordATurn(coord, currentCoord);
        const costOfTurn = isTurn ? 1 : 0;
        const intrinsicCost = isCoordGoalReached(coord) && !areCoordsEqual(currentCoord.coord, start) ? 0 : costGrid[coord.y][coord.x];
        const nextNode = {
          coord,
          cameFrom: currentCoord,
          currentCost: intrinsicCost + costOfMove + costOfTurn + currentCoord.currentCost
        };
        queue.enqueue(nextNode);
      }
    }
    if (currentCoord === void 0) {
      return [];
    }
    return coordLinkedListToArray(currentCoord);
  }
  function generateInitialCostGrid(gridSideLength, componentRenders) {
    const costGrid = generateGrid(gridSideLength, 0);
    addComponentsToCostGrid(costGrid, componentRenders);
    return costGrid;
  }
  function addComponentsToCostGrid(costGrid, componentRenders) {
    for (const componentRender of componentRenders) {
      const startY = componentRender.coord.y;
      const endY = componentRender.coord.y + componentRender.height;
      const startX = componentRender.coord.x;
      const endX = componentRender.coord.x + componentRender.width;
      for (let y = startY; y < endY + 1; y++) {
        for (let x = startX; x < endX + 1; x++) {
          costGrid[y][x] = Infinity;
        }
      }
    }
  }
  function addNetToCostGrid(costGrid, netRenders, pathCost) {
    for (const netRender of netRenders) {
      for (const path of netRender.paths) {
        for (const coord of path) {
          costGrid[coord.y][coord.x] = costGrid[coord.y][coord.x] + pathCost;
        }
      }
    }
  }
  function areCoordsEqual(a, b) {
    return a.x === b.x && a.y === b.y;
  }
  function arePointsCollinear(p1, p2, p3) {
    return (p2.y - p1.y) * (p3.x - p1.x) === (p3.y - p1.y) * (p2.x - p1.x);
  }
  function compressPaths(path) {
    if (path.length <= 2) {
      return path;
    }
    const acc = [];
    let current = 2;
    let startCoord = path[0];
    let lastCoord = path[1];
    acc.push(startCoord);
    acc.push(lastCoord);
    while (current < path.length) {
      const currentCoord = path[current];
      if (arePointsCollinear(startCoord, lastCoord, currentCoord)) {
        acc[acc.length - 1] = currentCoord;
        lastCoord = currentCoord;
      } else {
        acc.push(currentCoord);
        startCoord = lastCoord;
        lastCoord = currentCoord;
      }
      current++;
    }
    return acc;
  }
  function createNetRender(netId, optimizedNetList, pinRendersById, costGrid) {
    const pinLookupByNetId = optimizedNetList.pinIdsByNetId;
    const costOfCrossingAWire = BIAS_AGAINST_CROSSING_A_WIRE;
    const pathAcc = [];
    if (pinLookupByNetId[netId].length >= 2) {
      const [pinRender1, pinRender2] = pinLookupByNetId[netId].slice(0, 2).map((pinId) => pinRendersById[pinId]);
      const path = findShortestPath(costGrid, pinRender2.coord, [pinRender1.coord]);
      pathAcc.push(path);
      pinLookupByNetId[netId].slice(2).map((pinId) => pinRendersById[pinId]).forEach((pinRender) => {
        const goal = pathAcc.flat();
        const path2 = findShortestPath(costGrid, pinRender.coord, goal);
        pathAcc.push(path2);
      });
    }
    const res = {
      net: optimizedNetList.nets[netId],
      paths: pathAcc.map((path) => compressPaths(path)),
      color: colorFromString(netId.toString())
    };
    addNetToCostGrid(costGrid, [res], costOfCrossingAWire);
    return res;
  }
  function createPinRenderLookUpFromComponentRenders(componentRenders) {
    return Object.fromEntries(componentRenders.flatMap(({ pinRenders }) => pinRenders).map((pinRender) => [pinRender.pin.id, pinRender]));
  }
  function cellCoordFromIndex(index, gridSideCellsAmount) {
    return {
      x: index % gridSideCellsAmount,
      y: Math.floor(index / gridSideCellsAmount)
    };
  }
  function calculateAllComponentPositions(componentDimensions, cellDimension, gridSideCellsAmount) {
    return componentDimensions.map(
      ([width, height], index) => calculatePositionOfComponent(width, height, cellDimension, cellCoordFromIndex(index, gridSideCellsAmount))
    );
  }
  function calculatePositionOfComponent(width, height, cellDimension, cellIndex) {
    const leftPadding = Math.ceil((cellDimension - width) / 2);
    const topPadding = Math.ceil((cellDimension - height) / 2);
    return {
      x: leftPadding + cellIndex.x * cellDimension,
      y: topPadding + cellIndex.y * cellDimension
    };
  }
  function createNetListRender(optimizedNetList) {
    const gridSideCellsAmount = Math.ceil(Math.sqrt(Object.keys(optimizedNetList.components).length));
    const componentDimensions = calculateAllComponentDimensions(optimizedNetList);
    const paddingBetweenComponents = 7;
    const maxDimensionOfComponent = Math.max(...componentDimensions.flat());
    const cellDimension = maxDimensionOfComponent + paddingBetweenComponents * 2;
    const gridDimension = gridSideCellsAmount * cellDimension;
    const componentPositions = calculateAllComponentPositions(componentDimensions, cellDimension, gridSideCellsAmount);
    const componentRenders = createAllComponentRenders(componentPositions, optimizedNetList, componentDimensions);
    const pinRendersById = createPinRenderLookUpFromComponentRenders(componentRenders);
    const costGrid = generateInitialCostGrid(gridDimension, componentRenders);
    const netRenders = Object.keys(optimizedNetList.nets).map((netId) => createNetRender(netId, optimizedNetList, pinRendersById, costGrid));
    return {
      components: componentRenders,
      nets: netRenders,
      dimensions: gridDimension
    };
  }
  function $constructor(name, initializer2, params) {
    function init(inst, def) {
      var _a;
      Object.defineProperty(inst, "_zod", {
        value: inst._zod ?? {},
        enumerable: false
      });
      (_a = inst._zod).traits ?? (_a.traits = /* @__PURE__ */ new Set());
      inst._zod.traits.add(name);
      initializer2(inst, def);
      for (const k in _.prototype) {
        if (!(k in inst))
          Object.defineProperty(inst, k, { value: _.prototype[k].bind(inst) });
      }
      inst._zod.constr = _;
      inst._zod.def = def;
    }
    const Parent = params?.Parent ?? Object;
    class Definition extends Parent {
    }
    Object.defineProperty(Definition, "name", { value: name });
    function _(def) {
      var _a;
      const inst = params?.Parent ? new Definition() : this;
      init(inst, def);
      (_a = inst._zod).deferred ?? (_a.deferred = []);
      for (const fn of inst._zod.deferred) {
        fn();
      }
      return inst;
    }
    Object.defineProperty(_, "init", { value: init });
    Object.defineProperty(_, Symbol.hasInstance, {
      value: (inst) => {
        if (params?.Parent && inst instanceof params.Parent)
          return true;
        return inst?._zod?.traits?.has(name);
      }
    });
    Object.defineProperty(_, "name", { value: name });
    return _;
  }
  class $ZodAsyncError extends Error {
    constructor() {
      super(`Encountered Promise during synchronous parse. Use .parseAsync() instead.`);
    }
  }
  const globalConfig = {};
  function config(newConfig) {
    return globalConfig;
  }
  function getEnumValues(entries) {
    const numericValues = Object.values(entries).filter((v) => typeof v === "number");
    const values = Object.entries(entries).filter(([k, _]) => numericValues.indexOf(+k) === -1).map(([_, v]) => v);
    return values;
  }
  function jsonStringifyReplacer(_, value) {
    if (typeof value === "bigint")
      return value.toString();
    return value;
  }
  function cached(getter) {
    return {
      get value() {
        {
          const value = getter();
          Object.defineProperty(this, "value", { value });
          return value;
        }
      }
    };
  }
  function nullish(input) {
    return input === null || input === void 0;
  }
  function cleanRegex(source) {
    const start = source.startsWith("^") ? 1 : 0;
    const end = source.endsWith("$") ? source.length - 1 : source.length;
    return source.slice(start, end);
  }
  function defineLazy(object2, key, getter) {
    Object.defineProperty(object2, key, {
      get() {
        {
          const value = getter();
          object2[key] = value;
          return value;
        }
      },
      set(v) {
        Object.defineProperty(object2, key, {
          value: v
          // configurable: true,
        });
      },
      configurable: true
    });
  }
  function assignProp(target, prop, value) {
    Object.defineProperty(target, prop, {
      value,
      writable: true,
      enumerable: true,
      configurable: true
    });
  }
  function esc(str) {
    return JSON.stringify(str);
  }
  const captureStackTrace = Error.captureStackTrace ? Error.captureStackTrace : (..._args) => {
  };
  function isObject(data) {
    return typeof data === "object" && data !== null && !Array.isArray(data);
  }
  const allowsEval = cached(() => {
    if (typeof navigator !== "undefined" && navigator?.userAgent?.includes("Cloudflare")) {
      return false;
    }
    try {
      const F = Function;
      new F("");
      return true;
    } catch (_) {
      return false;
    }
  });
  function isPlainObject(o) {
    if (isObject(o) === false)
      return false;
    const ctor = o.constructor;
    if (ctor === void 0)
      return true;
    const prot = ctor.prototype;
    if (isObject(prot) === false)
      return false;
    if (Object.prototype.hasOwnProperty.call(prot, "isPrototypeOf") === false) {
      return false;
    }
    return true;
  }
  const propertyKeyTypes = /* @__PURE__ */ new Set(["string", "number", "symbol"]);
  function escapeRegex(str) {
    return str.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  }
  function clone(inst, def, params) {
    const cl = new inst._zod.constr(def ?? inst._zod.def);
    if (!def || params?.parent)
      cl._zod.parent = inst;
    return cl;
  }
  function normalizeParams(_params) {
    const params = _params;
    if (!params)
      return {};
    if (typeof params === "string")
      return { error: () => params };
    if (params?.message !== void 0) {
      if (params?.error !== void 0)
        throw new Error("Cannot specify both `message` and `error` params");
      params.error = params.message;
    }
    delete params.message;
    if (typeof params.error === "string")
      return { ...params, error: () => params.error };
    return params;
  }
  function optionalKeys(shape) {
    return Object.keys(shape).filter((k) => {
      return shape[k]._zod.optin === "optional" && shape[k]._zod.optout === "optional";
    });
  }
  function pick(schema, mask) {
    const newShape = {};
    const currDef = schema._zod.def;
    for (const key in mask) {
      if (!(key in currDef.shape)) {
        throw new Error(`Unrecognized key: "${key}"`);
      }
      if (!mask[key])
        continue;
      newShape[key] = currDef.shape[key];
    }
    return clone(schema, {
      ...schema._zod.def,
      shape: newShape,
      checks: []
    });
  }
  function omit(schema, mask) {
    const newShape = { ...schema._zod.def.shape };
    const currDef = schema._zod.def;
    for (const key in mask) {
      if (!(key in currDef.shape)) {
        throw new Error(`Unrecognized key: "${key}"`);
      }
      if (!mask[key])
        continue;
      delete newShape[key];
    }
    return clone(schema, {
      ...schema._zod.def,
      shape: newShape,
      checks: []
    });
  }
  function extend(schema, shape) {
    if (!isPlainObject(shape)) {
      throw new Error("Invalid input to extend: expected a plain object");
    }
    const def = {
      ...schema._zod.def,
      get shape() {
        const _shape = { ...schema._zod.def.shape, ...shape };
        assignProp(this, "shape", _shape);
        return _shape;
      },
      checks: []
      // delete existing checks
    };
    return clone(schema, def);
  }
  function merge(a, b) {
    return clone(a, {
      ...a._zod.def,
      get shape() {
        const _shape = { ...a._zod.def.shape, ...b._zod.def.shape };
        assignProp(this, "shape", _shape);
        return _shape;
      },
      catchall: b._zod.def.catchall,
      checks: []
      // delete existing checks
    });
  }
  function partial(Class, schema, mask) {
    const oldShape = schema._zod.def.shape;
    const shape = { ...oldShape };
    if (mask) {
      for (const key in mask) {
        if (!(key in oldShape)) {
          throw new Error(`Unrecognized key: "${key}"`);
        }
        if (!mask[key])
          continue;
        shape[key] = Class ? new Class({
          type: "optional",
          innerType: oldShape[key]
        }) : oldShape[key];
      }
    } else {
      for (const key in oldShape) {
        shape[key] = Class ? new Class({
          type: "optional",
          innerType: oldShape[key]
        }) : oldShape[key];
      }
    }
    return clone(schema, {
      ...schema._zod.def,
      shape,
      checks: []
    });
  }
  function required(Class, schema, mask) {
    const oldShape = schema._zod.def.shape;
    const shape = { ...oldShape };
    if (mask) {
      for (const key in mask) {
        if (!(key in shape)) {
          throw new Error(`Unrecognized key: "${key}"`);
        }
        if (!mask[key])
          continue;
        shape[key] = new Class({
          type: "nonoptional",
          innerType: oldShape[key]
        });
      }
    } else {
      for (const key in oldShape) {
        shape[key] = new Class({
          type: "nonoptional",
          innerType: oldShape[key]
        });
      }
    }
    return clone(schema, {
      ...schema._zod.def,
      shape,
      // optional: [],
      checks: []
    });
  }
  function aborted(x, startIndex = 0) {
    for (let i = startIndex; i < x.issues.length; i++) {
      if (x.issues[i]?.continue !== true)
        return true;
    }
    return false;
  }
  function prefixIssues(path, issues) {
    return issues.map((iss) => {
      var _a;
      (_a = iss).path ?? (_a.path = []);
      iss.path.unshift(path);
      return iss;
    });
  }
  function unwrapMessage(message) {
    return typeof message === "string" ? message : message?.message;
  }
  function finalizeIssue(iss, ctx, config2) {
    const full = { ...iss, path: iss.path ?? [] };
    if (!iss.message) {
      const message = unwrapMessage(iss.inst?._zod.def?.error?.(iss)) ?? unwrapMessage(ctx?.error?.(iss)) ?? unwrapMessage(config2.customError?.(iss)) ?? unwrapMessage(config2.localeError?.(iss)) ?? "Invalid input";
      full.message = message;
    }
    delete full.inst;
    delete full.continue;
    if (!ctx?.reportInput) {
      delete full.input;
    }
    return full;
  }
  function getLengthableOrigin(input) {
    if (Array.isArray(input))
      return "array";
    if (typeof input === "string")
      return "string";
    return "unknown";
  }
  function issue(...args) {
    const [iss, input, inst] = args;
    if (typeof iss === "string") {
      return {
        message: iss,
        code: "custom",
        input,
        inst
      };
    }
    return { ...iss };
  }
  const initializer$1 = (inst, def) => {
    inst.name = "$ZodError";
    Object.defineProperty(inst, "_zod", {
      value: inst._zod,
      enumerable: false
    });
    Object.defineProperty(inst, "issues", {
      value: def,
      enumerable: false
    });
    Object.defineProperty(inst, "message", {
      get() {
        return JSON.stringify(def, jsonStringifyReplacer, 2);
      },
      enumerable: true
      // configurable: false,
    });
    Object.defineProperty(inst, "toString", {
      value: () => inst.message,
      enumerable: false
    });
  };
  const $ZodError = $constructor("$ZodError", initializer$1);
  const $ZodRealError = $constructor("$ZodError", initializer$1, { Parent: Error });
  function flattenError(error, mapper = (issue2) => issue2.message) {
    const fieldErrors = {};
    const formErrors = [];
    for (const sub of error.issues) {
      if (sub.path.length > 0) {
        fieldErrors[sub.path[0]] = fieldErrors[sub.path[0]] || [];
        fieldErrors[sub.path[0]].push(mapper(sub));
      } else {
        formErrors.push(mapper(sub));
      }
    }
    return { formErrors, fieldErrors };
  }
  function formatError(error, _mapper) {
    const mapper = _mapper || function(issue2) {
      return issue2.message;
    };
    const fieldErrors = { _errors: [] };
    const processError = (error2) => {
      for (const issue2 of error2.issues) {
        if (issue2.code === "invalid_union" && issue2.errors.length) {
          issue2.errors.map((issues) => processError({ issues }));
        } else if (issue2.code === "invalid_key") {
          processError({ issues: issue2.issues });
        } else if (issue2.code === "invalid_element") {
          processError({ issues: issue2.issues });
        } else if (issue2.path.length === 0) {
          fieldErrors._errors.push(mapper(issue2));
        } else {
          let curr = fieldErrors;
          let i = 0;
          while (i < issue2.path.length) {
            const el = issue2.path[i];
            const terminal = i === issue2.path.length - 1;
            if (!terminal) {
              curr[el] = curr[el] || { _errors: [] };
            } else {
              curr[el] = curr[el] || { _errors: [] };
              curr[el]._errors.push(mapper(issue2));
            }
            curr = curr[el];
            i++;
          }
        }
      }
    };
    processError(error);
    return fieldErrors;
  }
  const _parse = (_Err) => (schema, value, _ctx, _params) => {
    const ctx = _ctx ? Object.assign(_ctx, { async: false }) : { async: false };
    const result = schema._zod.run({ value, issues: [] }, ctx);
    if (result instanceof Promise) {
      throw new $ZodAsyncError();
    }
    if (result.issues.length) {
      const e = new (_params?.Err ?? _Err)(result.issues.map((iss) => finalizeIssue(iss, ctx, config())));
      captureStackTrace(e, _params?.callee);
      throw e;
    }
    return result.value;
  };
  const _parseAsync = (_Err) => async (schema, value, _ctx, params) => {
    const ctx = _ctx ? Object.assign(_ctx, { async: true }) : { async: true };
    let result = schema._zod.run({ value, issues: [] }, ctx);
    if (result instanceof Promise)
      result = await result;
    if (result.issues.length) {
      const e = new (params?.Err ?? _Err)(result.issues.map((iss) => finalizeIssue(iss, ctx, config())));
      captureStackTrace(e, params?.callee);
      throw e;
    }
    return result.value;
  };
  const _safeParse = (_Err) => (schema, value, _ctx) => {
    const ctx = _ctx ? { ..._ctx, async: false } : { async: false };
    const result = schema._zod.run({ value, issues: [] }, ctx);
    if (result instanceof Promise) {
      throw new $ZodAsyncError();
    }
    return result.issues.length ? {
      success: false,
      error: new (_Err ?? $ZodError)(result.issues.map((iss) => finalizeIssue(iss, ctx, config())))
    } : { success: true, data: result.value };
  };
  const safeParse$1 = /* @__PURE__ */ _safeParse($ZodRealError);
  const _safeParseAsync = (_Err) => async (schema, value, _ctx) => {
    const ctx = _ctx ? Object.assign(_ctx, { async: true }) : { async: true };
    let result = schema._zod.run({ value, issues: [] }, ctx);
    if (result instanceof Promise)
      result = await result;
    return result.issues.length ? {
      success: false,
      error: new _Err(result.issues.map((iss) => finalizeIssue(iss, ctx, config())))
    } : { success: true, data: result.value };
  };
  const safeParseAsync$1 = /* @__PURE__ */ _safeParseAsync($ZodRealError);
  const cuid = /^[cC][^\s-]{8,}$/;
  const cuid2 = /^[0-9a-z]+$/;
  const ulid = /^[0-9A-HJKMNP-TV-Za-hjkmnp-tv-z]{26}$/;
  const xid = /^[0-9a-vA-V]{20}$/;
  const ksuid = /^[A-Za-z0-9]{27}$/;
  const nanoid = /^[a-zA-Z0-9_-]{21}$/;
  const duration$1 = /^P(?:(\d+W)|(?!.*W)(?=\d|T\d)(\d+Y)?(\d+M)?(\d+D)?(T(?=\d)(\d+H)?(\d+M)?(\d+([.,]\d+)?S)?)?)$/;
  const guid = /^([0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12})$/;
  const uuid = (version2) => {
    if (!version2)
      return /^([0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[1-8][0-9a-fA-F]{3}-[89abAB][0-9a-fA-F]{3}-[0-9a-fA-F]{12}|00000000-0000-0000-0000-000000000000)$/;
    return new RegExp(`^([0-9a-fA-F]{8}-[0-9a-fA-F]{4}-${version2}[0-9a-fA-F]{3}-[89abAB][0-9a-fA-F]{3}-[0-9a-fA-F]{12})$`);
  };
  const email = /^(?!\.)(?!.*\.\.)([A-Za-z0-9_'+\-\.]*)[A-Za-z0-9_+-]@([A-Za-z0-9][A-Za-z0-9\-]*\.)+[A-Za-z]{2,}$/;
  const _emoji$1 = `^(\\p{Extended_Pictographic}|\\p{Emoji_Component})+$`;
  function emoji() {
    return new RegExp(_emoji$1, "u");
  }
  const ipv4 = /^(?:(?:25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\.){3}(?:25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])$/;
  const ipv6 = /^(([0-9a-fA-F]{1,4}:){7}[0-9a-fA-F]{1,4}|::|([0-9a-fA-F]{1,4})?::([0-9a-fA-F]{1,4}:?){0,6})$/;
  const cidrv4 = /^((25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\.){3}(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\/([0-9]|[1-2][0-9]|3[0-2])$/;
  const cidrv6 = /^(([0-9a-fA-F]{1,4}:){7}[0-9a-fA-F]{1,4}|::|([0-9a-fA-F]{1,4})?::([0-9a-fA-F]{1,4}:?){0,6})\/(12[0-8]|1[01][0-9]|[1-9]?[0-9])$/;
  const base64 = /^$|^(?:[0-9a-zA-Z+/]{4})*(?:(?:[0-9a-zA-Z+/]{2}==)|(?:[0-9a-zA-Z+/]{3}=))?$/;
  const base64url = /^[A-Za-z0-9_-]*$/;
  const hostname = /^([a-zA-Z0-9-]+\.)*[a-zA-Z0-9-]+$/;
  const e164 = /^\+(?:[0-9]){6,14}[0-9]$/;
  const dateSource = `(?:(?:\\d\\d[2468][048]|\\d\\d[13579][26]|\\d\\d0[48]|[02468][048]00|[13579][26]00)-02-29|\\d{4}-(?:(?:0[13578]|1[02])-(?:0[1-9]|[12]\\d|3[01])|(?:0[469]|11)-(?:0[1-9]|[12]\\d|30)|(?:02)-(?:0[1-9]|1\\d|2[0-8])))`;
  const date$2 = /* @__PURE__ */ new RegExp(`^${dateSource}$`);
  function timeSource(args) {
    const hhmm = `(?:[01]\\d|2[0-3]):[0-5]\\d`;
    const regex = typeof args.precision === "number" ? args.precision === -1 ? `${hhmm}` : args.precision === 0 ? `${hhmm}:[0-5]\\d` : `${hhmm}:[0-5]\\d\\.\\d{${args.precision}}` : `${hhmm}(?::[0-5]\\d(?:\\.\\d+)?)?`;
    return regex;
  }
  function time$1(args) {
    return new RegExp(`^${timeSource(args)}$`);
  }
  function datetime$1(args) {
    const time2 = timeSource({ precision: args.precision });
    const opts = ["Z"];
    if (args.local)
      opts.push("");
    if (args.offset)
      opts.push(`([+-]\\d{2}:\\d{2})`);
    const timeRegex = `${time2}(?:${opts.join("|")})`;
    return new RegExp(`^${dateSource}T(?:${timeRegex})$`);
  }
  const string$2 = (params) => {
    const regex = params ? `[\\s\\S]{${params?.minimum ?? 0},${params?.maximum ?? ""}}` : `[\\s\\S]*`;
    return new RegExp(`^${regex}$`);
  };
  const lowercase = /^[^A-Z]*$/;
  const uppercase = /^[^a-z]*$/;
  const $ZodCheck = /* @__PURE__ */ $constructor("$ZodCheck", (inst, def) => {
    var _a;
    inst._zod ?? (inst._zod = {});
    inst._zod.def = def;
    (_a = inst._zod).onattach ?? (_a.onattach = []);
  });
  const numericOriginMap = {
    number: "number",
    bigint: "bigint",
    object: "date"
  };
  const $ZodCheckLessThan = /* @__PURE__ */ $constructor("$ZodCheckLessThan", (inst, def) => {
    $ZodCheck.init(inst, def);
    const origin = numericOriginMap[typeof def.value];
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      const curr = (def.inclusive ? bag.maximum : bag.exclusiveMaximum) ?? Number.POSITIVE_INFINITY;
      if (def.value < curr) {
        if (def.inclusive)
          bag.maximum = def.value;
        else
          bag.exclusiveMaximum = def.value;
      }
    });
    inst._zod.check = (payload) => {
      if (def.inclusive ? payload.value <= def.value : payload.value < def.value) {
        return;
      }
      payload.issues.push({
        origin,
        code: "too_big",
        maximum: def.value,
        input: payload.value,
        inclusive: def.inclusive,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckGreaterThan = /* @__PURE__ */ $constructor("$ZodCheckGreaterThan", (inst, def) => {
    $ZodCheck.init(inst, def);
    const origin = numericOriginMap[typeof def.value];
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      const curr = (def.inclusive ? bag.minimum : bag.exclusiveMinimum) ?? Number.NEGATIVE_INFINITY;
      if (def.value > curr) {
        if (def.inclusive)
          bag.minimum = def.value;
        else
          bag.exclusiveMinimum = def.value;
      }
    });
    inst._zod.check = (payload) => {
      if (def.inclusive ? payload.value >= def.value : payload.value > def.value) {
        return;
      }
      payload.issues.push({
        origin,
        code: "too_small",
        minimum: def.value,
        input: payload.value,
        inclusive: def.inclusive,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckMaxLength = /* @__PURE__ */ $constructor("$ZodCheckMaxLength", (inst, def) => {
    var _a;
    $ZodCheck.init(inst, def);
    (_a = inst._zod.def).when ?? (_a.when = (payload) => {
      const val = payload.value;
      return !nullish(val) && val.length !== void 0;
    });
    inst._zod.onattach.push((inst2) => {
      const curr = inst2._zod.bag.maximum ?? Number.POSITIVE_INFINITY;
      if (def.maximum < curr)
        inst2._zod.bag.maximum = def.maximum;
    });
    inst._zod.check = (payload) => {
      const input = payload.value;
      const length = input.length;
      if (length <= def.maximum)
        return;
      const origin = getLengthableOrigin(input);
      payload.issues.push({
        origin,
        code: "too_big",
        maximum: def.maximum,
        inclusive: true,
        input,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckMinLength = /* @__PURE__ */ $constructor("$ZodCheckMinLength", (inst, def) => {
    var _a;
    $ZodCheck.init(inst, def);
    (_a = inst._zod.def).when ?? (_a.when = (payload) => {
      const val = payload.value;
      return !nullish(val) && val.length !== void 0;
    });
    inst._zod.onattach.push((inst2) => {
      const curr = inst2._zod.bag.minimum ?? Number.NEGATIVE_INFINITY;
      if (def.minimum > curr)
        inst2._zod.bag.minimum = def.minimum;
    });
    inst._zod.check = (payload) => {
      const input = payload.value;
      const length = input.length;
      if (length >= def.minimum)
        return;
      const origin = getLengthableOrigin(input);
      payload.issues.push({
        origin,
        code: "too_small",
        minimum: def.minimum,
        inclusive: true,
        input,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckLengthEquals = /* @__PURE__ */ $constructor("$ZodCheckLengthEquals", (inst, def) => {
    var _a;
    $ZodCheck.init(inst, def);
    (_a = inst._zod.def).when ?? (_a.when = (payload) => {
      const val = payload.value;
      return !nullish(val) && val.length !== void 0;
    });
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      bag.minimum = def.length;
      bag.maximum = def.length;
      bag.length = def.length;
    });
    inst._zod.check = (payload) => {
      const input = payload.value;
      const length = input.length;
      if (length === def.length)
        return;
      const origin = getLengthableOrigin(input);
      const tooBig = length > def.length;
      payload.issues.push({
        origin,
        ...tooBig ? { code: "too_big", maximum: def.length } : { code: "too_small", minimum: def.length },
        inclusive: true,
        exact: true,
        input: payload.value,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckStringFormat = /* @__PURE__ */ $constructor("$ZodCheckStringFormat", (inst, def) => {
    var _a, _b;
    $ZodCheck.init(inst, def);
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      bag.format = def.format;
      if (def.pattern) {
        bag.patterns ?? (bag.patterns = /* @__PURE__ */ new Set());
        bag.patterns.add(def.pattern);
      }
    });
    if (def.pattern)
      (_a = inst._zod).check ?? (_a.check = (payload) => {
        def.pattern.lastIndex = 0;
        if (def.pattern.test(payload.value))
          return;
        payload.issues.push({
          origin: "string",
          code: "invalid_format",
          format: def.format,
          input: payload.value,
          ...def.pattern ? { pattern: def.pattern.toString() } : {},
          inst,
          continue: !def.abort
        });
      });
    else
      (_b = inst._zod).check ?? (_b.check = () => {
      });
  });
  const $ZodCheckRegex = /* @__PURE__ */ $constructor("$ZodCheckRegex", (inst, def) => {
    $ZodCheckStringFormat.init(inst, def);
    inst._zod.check = (payload) => {
      def.pattern.lastIndex = 0;
      if (def.pattern.test(payload.value))
        return;
      payload.issues.push({
        origin: "string",
        code: "invalid_format",
        format: "regex",
        input: payload.value,
        pattern: def.pattern.toString(),
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckLowerCase = /* @__PURE__ */ $constructor("$ZodCheckLowerCase", (inst, def) => {
    def.pattern ?? (def.pattern = lowercase);
    $ZodCheckStringFormat.init(inst, def);
  });
  const $ZodCheckUpperCase = /* @__PURE__ */ $constructor("$ZodCheckUpperCase", (inst, def) => {
    def.pattern ?? (def.pattern = uppercase);
    $ZodCheckStringFormat.init(inst, def);
  });
  const $ZodCheckIncludes = /* @__PURE__ */ $constructor("$ZodCheckIncludes", (inst, def) => {
    $ZodCheck.init(inst, def);
    const escapedRegex = escapeRegex(def.includes);
    const pattern = new RegExp(typeof def.position === "number" ? `^.{${def.position}}${escapedRegex}` : escapedRegex);
    def.pattern = pattern;
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      bag.patterns ?? (bag.patterns = /* @__PURE__ */ new Set());
      bag.patterns.add(pattern);
    });
    inst._zod.check = (payload) => {
      if (payload.value.includes(def.includes, def.position))
        return;
      payload.issues.push({
        origin: "string",
        code: "invalid_format",
        format: "includes",
        includes: def.includes,
        input: payload.value,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckStartsWith = /* @__PURE__ */ $constructor("$ZodCheckStartsWith", (inst, def) => {
    $ZodCheck.init(inst, def);
    const pattern = new RegExp(`^${escapeRegex(def.prefix)}.*`);
    def.pattern ?? (def.pattern = pattern);
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      bag.patterns ?? (bag.patterns = /* @__PURE__ */ new Set());
      bag.patterns.add(pattern);
    });
    inst._zod.check = (payload) => {
      if (payload.value.startsWith(def.prefix))
        return;
      payload.issues.push({
        origin: "string",
        code: "invalid_format",
        format: "starts_with",
        prefix: def.prefix,
        input: payload.value,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckEndsWith = /* @__PURE__ */ $constructor("$ZodCheckEndsWith", (inst, def) => {
    $ZodCheck.init(inst, def);
    const pattern = new RegExp(`.*${escapeRegex(def.suffix)}$`);
    def.pattern ?? (def.pattern = pattern);
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      bag.patterns ?? (bag.patterns = /* @__PURE__ */ new Set());
      bag.patterns.add(pattern);
    });
    inst._zod.check = (payload) => {
      if (payload.value.endsWith(def.suffix))
        return;
      payload.issues.push({
        origin: "string",
        code: "invalid_format",
        format: "ends_with",
        suffix: def.suffix,
        input: payload.value,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodCheckOverwrite = /* @__PURE__ */ $constructor("$ZodCheckOverwrite", (inst, def) => {
    $ZodCheck.init(inst, def);
    inst._zod.check = (payload) => {
      payload.value = def.tx(payload.value);
    };
  });
  class Doc {
    constructor(args = []) {
      this.content = [];
      this.indent = 0;
      if (this)
        this.args = args;
    }
    indented(fn) {
      this.indent += 1;
      fn(this);
      this.indent -= 1;
    }
    write(arg) {
      if (typeof arg === "function") {
        arg(this, { execution: "sync" });
        arg(this, { execution: "async" });
        return;
      }
      const content = arg;
      const lines = content.split("\n").filter((x) => x);
      const minIndent = Math.min(...lines.map((x) => x.length - x.trimStart().length));
      const dedented = lines.map((x) => x.slice(minIndent)).map((x) => " ".repeat(this.indent * 2) + x);
      for (const line of dedented) {
        this.content.push(line);
      }
    }
    compile() {
      const F = Function;
      const args = this?.args;
      const content = this?.content ?? [``];
      const lines = [...content.map((x) => `  ${x}`)];
      return new F(...args, lines.join("\n"));
    }
  }
  const version = {
    major: 4,
    minor: 0,
    patch: 5
  };
  const $ZodType = /* @__PURE__ */ $constructor("$ZodType", (inst, def) => {
    var _a;
    inst ?? (inst = {});
    inst._zod.def = def;
    inst._zod.bag = inst._zod.bag || {};
    inst._zod.version = version;
    const checks = [...inst._zod.def.checks ?? []];
    if (inst._zod.traits.has("$ZodCheck")) {
      checks.unshift(inst);
    }
    for (const ch of checks) {
      for (const fn of ch._zod.onattach) {
        fn(inst);
      }
    }
    if (checks.length === 0) {
      (_a = inst._zod).deferred ?? (_a.deferred = []);
      inst._zod.deferred?.push(() => {
        inst._zod.run = inst._zod.parse;
      });
    } else {
      const runChecks = (payload, checks2, ctx) => {
        let isAborted = aborted(payload);
        let asyncResult;
        for (const ch of checks2) {
          if (ch._zod.def.when) {
            const shouldRun = ch._zod.def.when(payload);
            if (!shouldRun)
              continue;
          } else if (isAborted) {
            continue;
          }
          const currLen = payload.issues.length;
          const _ = ch._zod.check(payload);
          if (_ instanceof Promise && ctx?.async === false) {
            throw new $ZodAsyncError();
          }
          if (asyncResult || _ instanceof Promise) {
            asyncResult = (asyncResult ?? Promise.resolve()).then(async () => {
              await _;
              const nextLen = payload.issues.length;
              if (nextLen === currLen)
                return;
              if (!isAborted)
                isAborted = aborted(payload, currLen);
            });
          } else {
            const nextLen = payload.issues.length;
            if (nextLen === currLen)
              continue;
            if (!isAborted)
              isAborted = aborted(payload, currLen);
          }
        }
        if (asyncResult) {
          return asyncResult.then(() => {
            return payload;
          });
        }
        return payload;
      };
      inst._zod.run = (payload, ctx) => {
        const result = inst._zod.parse(payload, ctx);
        if (result instanceof Promise) {
          if (ctx.async === false)
            throw new $ZodAsyncError();
          return result.then((result2) => runChecks(result2, checks, ctx));
        }
        return runChecks(result, checks, ctx);
      };
    }
    inst["~standard"] = {
      validate: (value) => {
        try {
          const r = safeParse$1(inst, value);
          return r.success ? { value: r.data } : { issues: r.error?.issues };
        } catch (_) {
          return safeParseAsync$1(inst, value).then((r) => r.success ? { value: r.data } : { issues: r.error?.issues });
        }
      },
      vendor: "zod",
      version: 1
    };
  });
  const $ZodString = /* @__PURE__ */ $constructor("$ZodString", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.pattern = [...inst?._zod.bag?.patterns ?? []].pop() ?? string$2(inst._zod.bag);
    inst._zod.parse = (payload, _) => {
      if (def.coerce)
        try {
          payload.value = String(payload.value);
        } catch (_2) {
        }
      if (typeof payload.value === "string")
        return payload;
      payload.issues.push({
        expected: "string",
        code: "invalid_type",
        input: payload.value,
        inst
      });
      return payload;
    };
  });
  const $ZodStringFormat = /* @__PURE__ */ $constructor("$ZodStringFormat", (inst, def) => {
    $ZodCheckStringFormat.init(inst, def);
    $ZodString.init(inst, def);
  });
  const $ZodGUID = /* @__PURE__ */ $constructor("$ZodGUID", (inst, def) => {
    def.pattern ?? (def.pattern = guid);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodUUID = /* @__PURE__ */ $constructor("$ZodUUID", (inst, def) => {
    if (def.version) {
      const versionMap = {
        v1: 1,
        v2: 2,
        v3: 3,
        v4: 4,
        v5: 5,
        v6: 6,
        v7: 7,
        v8: 8
      };
      const v = versionMap[def.version];
      if (v === void 0)
        throw new Error(`Invalid UUID version: "${def.version}"`);
      def.pattern ?? (def.pattern = uuid(v));
    } else
      def.pattern ?? (def.pattern = uuid());
    $ZodStringFormat.init(inst, def);
  });
  const $ZodEmail = /* @__PURE__ */ $constructor("$ZodEmail", (inst, def) => {
    def.pattern ?? (def.pattern = email);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodURL = /* @__PURE__ */ $constructor("$ZodURL", (inst, def) => {
    $ZodStringFormat.init(inst, def);
    inst._zod.check = (payload) => {
      try {
        const orig = payload.value;
        const url = new URL(orig);
        const href = url.href;
        if (def.hostname) {
          def.hostname.lastIndex = 0;
          if (!def.hostname.test(url.hostname)) {
            payload.issues.push({
              code: "invalid_format",
              format: "url",
              note: "Invalid hostname",
              pattern: hostname.source,
              input: payload.value,
              inst,
              continue: !def.abort
            });
          }
        }
        if (def.protocol) {
          def.protocol.lastIndex = 0;
          if (!def.protocol.test(url.protocol.endsWith(":") ? url.protocol.slice(0, -1) : url.protocol)) {
            payload.issues.push({
              code: "invalid_format",
              format: "url",
              note: "Invalid protocol",
              pattern: def.protocol.source,
              input: payload.value,
              inst,
              continue: !def.abort
            });
          }
        }
        if (!orig.endsWith("/") && href.endsWith("/")) {
          payload.value = href.slice(0, -1);
        } else {
          payload.value = href;
        }
        return;
      } catch (_) {
        payload.issues.push({
          code: "invalid_format",
          format: "url",
          input: payload.value,
          inst,
          continue: !def.abort
        });
      }
    };
  });
  const $ZodEmoji = /* @__PURE__ */ $constructor("$ZodEmoji", (inst, def) => {
    def.pattern ?? (def.pattern = emoji());
    $ZodStringFormat.init(inst, def);
  });
  const $ZodNanoID = /* @__PURE__ */ $constructor("$ZodNanoID", (inst, def) => {
    def.pattern ?? (def.pattern = nanoid);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodCUID = /* @__PURE__ */ $constructor("$ZodCUID", (inst, def) => {
    def.pattern ?? (def.pattern = cuid);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodCUID2 = /* @__PURE__ */ $constructor("$ZodCUID2", (inst, def) => {
    def.pattern ?? (def.pattern = cuid2);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodULID = /* @__PURE__ */ $constructor("$ZodULID", (inst, def) => {
    def.pattern ?? (def.pattern = ulid);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodXID = /* @__PURE__ */ $constructor("$ZodXID", (inst, def) => {
    def.pattern ?? (def.pattern = xid);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodKSUID = /* @__PURE__ */ $constructor("$ZodKSUID", (inst, def) => {
    def.pattern ?? (def.pattern = ksuid);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodISODateTime = /* @__PURE__ */ $constructor("$ZodISODateTime", (inst, def) => {
    def.pattern ?? (def.pattern = datetime$1(def));
    $ZodStringFormat.init(inst, def);
  });
  const $ZodISODate = /* @__PURE__ */ $constructor("$ZodISODate", (inst, def) => {
    def.pattern ?? (def.pattern = date$2);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodISOTime = /* @__PURE__ */ $constructor("$ZodISOTime", (inst, def) => {
    def.pattern ?? (def.pattern = time$1(def));
    $ZodStringFormat.init(inst, def);
  });
  const $ZodISODuration = /* @__PURE__ */ $constructor("$ZodISODuration", (inst, def) => {
    def.pattern ?? (def.pattern = duration$1);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodIPv4 = /* @__PURE__ */ $constructor("$ZodIPv4", (inst, def) => {
    def.pattern ?? (def.pattern = ipv4);
    $ZodStringFormat.init(inst, def);
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      bag.format = `ipv4`;
    });
  });
  const $ZodIPv6 = /* @__PURE__ */ $constructor("$ZodIPv6", (inst, def) => {
    def.pattern ?? (def.pattern = ipv6);
    $ZodStringFormat.init(inst, def);
    inst._zod.onattach.push((inst2) => {
      const bag = inst2._zod.bag;
      bag.format = `ipv6`;
    });
    inst._zod.check = (payload) => {
      try {
        new URL(`http://[${payload.value}]`);
      } catch {
        payload.issues.push({
          code: "invalid_format",
          format: "ipv6",
          input: payload.value,
          inst,
          continue: !def.abort
        });
      }
    };
  });
  const $ZodCIDRv4 = /* @__PURE__ */ $constructor("$ZodCIDRv4", (inst, def) => {
    def.pattern ?? (def.pattern = cidrv4);
    $ZodStringFormat.init(inst, def);
  });
  const $ZodCIDRv6 = /* @__PURE__ */ $constructor("$ZodCIDRv6", (inst, def) => {
    def.pattern ?? (def.pattern = cidrv6);
    $ZodStringFormat.init(inst, def);
    inst._zod.check = (payload) => {
      const [address, prefix] = payload.value.split("/");
      try {
        if (!prefix)
          throw new Error();
        const prefixNum = Number(prefix);
        if (`${prefixNum}` !== prefix)
          throw new Error();
        if (prefixNum < 0 || prefixNum > 128)
          throw new Error();
        new URL(`http://[${address}]`);
      } catch {
        payload.issues.push({
          code: "invalid_format",
          format: "cidrv6",
          input: payload.value,
          inst,
          continue: !def.abort
        });
      }
    };
  });
  function isValidBase64(data) {
    if (data === "")
      return true;
    if (data.length % 4 !== 0)
      return false;
    try {
      atob(data);
      return true;
    } catch {
      return false;
    }
  }
  const $ZodBase64 = /* @__PURE__ */ $constructor("$ZodBase64", (inst, def) => {
    def.pattern ?? (def.pattern = base64);
    $ZodStringFormat.init(inst, def);
    inst._zod.onattach.push((inst2) => {
      inst2._zod.bag.contentEncoding = "base64";
    });
    inst._zod.check = (payload) => {
      if (isValidBase64(payload.value))
        return;
      payload.issues.push({
        code: "invalid_format",
        format: "base64",
        input: payload.value,
        inst,
        continue: !def.abort
      });
    };
  });
  function isValidBase64URL(data) {
    if (!base64url.test(data))
      return false;
    const base642 = data.replace(/[-_]/g, (c) => c === "-" ? "+" : "/");
    const padded = base642.padEnd(Math.ceil(base642.length / 4) * 4, "=");
    return isValidBase64(padded);
  }
  const $ZodBase64URL = /* @__PURE__ */ $constructor("$ZodBase64URL", (inst, def) => {
    def.pattern ?? (def.pattern = base64url);
    $ZodStringFormat.init(inst, def);
    inst._zod.onattach.push((inst2) => {
      inst2._zod.bag.contentEncoding = "base64url";
    });
    inst._zod.check = (payload) => {
      if (isValidBase64URL(payload.value))
        return;
      payload.issues.push({
        code: "invalid_format",
        format: "base64url",
        input: payload.value,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodE164 = /* @__PURE__ */ $constructor("$ZodE164", (inst, def) => {
    def.pattern ?? (def.pattern = e164);
    $ZodStringFormat.init(inst, def);
  });
  function isValidJWT(token, algorithm = null) {
    try {
      const tokensParts = token.split(".");
      if (tokensParts.length !== 3)
        return false;
      const [header] = tokensParts;
      if (!header)
        return false;
      const parsedHeader = JSON.parse(atob(header));
      if ("typ" in parsedHeader && parsedHeader?.typ !== "JWT")
        return false;
      if (!parsedHeader.alg)
        return false;
      if (algorithm && (!("alg" in parsedHeader) || parsedHeader.alg !== algorithm))
        return false;
      return true;
    } catch {
      return false;
    }
  }
  const $ZodJWT = /* @__PURE__ */ $constructor("$ZodJWT", (inst, def) => {
    $ZodStringFormat.init(inst, def);
    inst._zod.check = (payload) => {
      if (isValidJWT(payload.value, def.alg))
        return;
      payload.issues.push({
        code: "invalid_format",
        format: "jwt",
        input: payload.value,
        inst,
        continue: !def.abort
      });
    };
  });
  const $ZodUnknown = /* @__PURE__ */ $constructor("$ZodUnknown", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.parse = (payload) => payload;
  });
  const $ZodNever = /* @__PURE__ */ $constructor("$ZodNever", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.parse = (payload, _ctx) => {
      payload.issues.push({
        expected: "never",
        code: "invalid_type",
        input: payload.value,
        inst
      });
      return payload;
    };
  });
  const $ZodDate = /* @__PURE__ */ $constructor("$ZodDate", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.parse = (payload, _ctx) => {
      if (def.coerce) {
        try {
          payload.value = new Date(payload.value);
        } catch (_err) {
        }
      }
      const input = payload.value;
      const isDate = input instanceof Date;
      const isValidDate = isDate && !Number.isNaN(input.getTime());
      if (isValidDate)
        return payload;
      payload.issues.push({
        expected: "date",
        code: "invalid_type",
        input,
        ...isDate ? { received: "Invalid Date" } : {},
        inst
      });
      return payload;
    };
  });
  function handleArrayResult(result, final, index) {
    if (result.issues.length) {
      final.issues.push(...prefixIssues(index, result.issues));
    }
    final.value[index] = result.value;
  }
  const $ZodArray = /* @__PURE__ */ $constructor("$ZodArray", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.parse = (payload, ctx) => {
      const input = payload.value;
      if (!Array.isArray(input)) {
        payload.issues.push({
          expected: "array",
          code: "invalid_type",
          input,
          inst
        });
        return payload;
      }
      payload.value = Array(input.length);
      const proms = [];
      for (let i = 0; i < input.length; i++) {
        const item = input[i];
        const result = def.element._zod.run({
          value: item,
          issues: []
        }, ctx);
        if (result instanceof Promise) {
          proms.push(result.then((result2) => handleArrayResult(result2, payload, i)));
        } else {
          handleArrayResult(result, payload, i);
        }
      }
      if (proms.length) {
        return Promise.all(proms).then(() => payload);
      }
      return payload;
    };
  });
  function handleObjectResult(result, final, key) {
    if (result.issues.length) {
      final.issues.push(...prefixIssues(key, result.issues));
    }
    final.value[key] = result.value;
  }
  function handleOptionalObjectResult(result, final, key, input) {
    if (result.issues.length) {
      if (input[key] === void 0) {
        if (key in input) {
          final.value[key] = void 0;
        } else {
          final.value[key] = result.value;
        }
      } else {
        final.issues.push(...prefixIssues(key, result.issues));
      }
    } else if (result.value === void 0) {
      if (key in input)
        final.value[key] = void 0;
    } else {
      final.value[key] = result.value;
    }
  }
  const $ZodObject = /* @__PURE__ */ $constructor("$ZodObject", (inst, def) => {
    $ZodType.init(inst, def);
    const _normalized = cached(() => {
      const keys = Object.keys(def.shape);
      for (const k of keys) {
        if (!(def.shape[k] instanceof $ZodType)) {
          throw new Error(`Invalid element at key "${k}": expected a Zod schema`);
        }
      }
      const okeys = optionalKeys(def.shape);
      return {
        shape: def.shape,
        keys,
        keySet: new Set(keys),
        numKeys: keys.length,
        optionalKeys: new Set(okeys)
      };
    });
    defineLazy(inst._zod, "propValues", () => {
      const shape = def.shape;
      const propValues = {};
      for (const key in shape) {
        const field = shape[key]._zod;
        if (field.values) {
          propValues[key] ?? (propValues[key] = /* @__PURE__ */ new Set());
          for (const v of field.values)
            propValues[key].add(v);
        }
      }
      return propValues;
    });
    const generateFastpass = (shape) => {
      const doc = new Doc(["shape", "payload", "ctx"]);
      const normalized = _normalized.value;
      const parseStr = (key) => {
        const k = esc(key);
        return `shape[${k}]._zod.run({ value: input[${k}], issues: [] }, ctx)`;
      };
      doc.write(`const input = payload.value;`);
      const ids = /* @__PURE__ */ Object.create(null);
      let counter = 0;
      for (const key of normalized.keys) {
        ids[key] = `key_${counter++}`;
      }
      doc.write(`const newResult = {}`);
      for (const key of normalized.keys) {
        if (normalized.optionalKeys.has(key)) {
          const id = ids[key];
          doc.write(`const ${id} = ${parseStr(key)};`);
          const k = esc(key);
          doc.write(`
        if (${id}.issues.length) {
          if (input[${k}] === undefined) {
            if (${k} in input) {
              newResult[${k}] = undefined;
            }
          } else {
            payload.issues = payload.issues.concat(
              ${id}.issues.map((iss) => ({
                ...iss,
                path: iss.path ? [${k}, ...iss.path] : [${k}],
              }))
            );
          }
        } else if (${id}.value === undefined) {
          if (${k} in input) newResult[${k}] = undefined;
        } else {
          newResult[${k}] = ${id}.value;
        }
        `);
        } else {
          const id = ids[key];
          doc.write(`const ${id} = ${parseStr(key)};`);
          doc.write(`
          if (${id}.issues.length) payload.issues = payload.issues.concat(${id}.issues.map(iss => ({
            ...iss,
            path: iss.path ? [${esc(key)}, ...iss.path] : [${esc(key)}]
          })));`);
          doc.write(`newResult[${esc(key)}] = ${id}.value`);
        }
      }
      doc.write(`payload.value = newResult;`);
      doc.write(`return payload;`);
      const fn = doc.compile();
      return (payload, ctx) => fn(shape, payload, ctx);
    };
    let fastpass;
    const isObject$1 = isObject;
    const jit = !globalConfig.jitless;
    const allowsEval$1 = allowsEval;
    const fastEnabled = jit && allowsEval$1.value;
    const catchall = def.catchall;
    let value;
    inst._zod.parse = (payload, ctx) => {
      value ?? (value = _normalized.value);
      const input = payload.value;
      if (!isObject$1(input)) {
        payload.issues.push({
          expected: "object",
          code: "invalid_type",
          input,
          inst
        });
        return payload;
      }
      const proms = [];
      if (jit && fastEnabled && ctx?.async === false && ctx.jitless !== true) {
        if (!fastpass)
          fastpass = generateFastpass(def.shape);
        payload = fastpass(payload, ctx);
      } else {
        payload.value = {};
        const shape = value.shape;
        for (const key of value.keys) {
          const el = shape[key];
          const r = el._zod.run({ value: input[key], issues: [] }, ctx);
          const isOptional = el._zod.optin === "optional" && el._zod.optout === "optional";
          if (r instanceof Promise) {
            proms.push(r.then((r2) => isOptional ? handleOptionalObjectResult(r2, payload, key, input) : handleObjectResult(r2, payload, key)));
          } else if (isOptional) {
            handleOptionalObjectResult(r, payload, key, input);
          } else {
            handleObjectResult(r, payload, key);
          }
        }
      }
      if (!catchall) {
        return proms.length ? Promise.all(proms).then(() => payload) : payload;
      }
      const unrecognized = [];
      const keySet = value.keySet;
      const _catchall = catchall._zod;
      const t = _catchall.def.type;
      for (const key of Object.keys(input)) {
        if (keySet.has(key))
          continue;
        if (t === "never") {
          unrecognized.push(key);
          continue;
        }
        const r = _catchall.run({ value: input[key], issues: [] }, ctx);
        if (r instanceof Promise) {
          proms.push(r.then((r2) => handleObjectResult(r2, payload, key)));
        } else {
          handleObjectResult(r, payload, key);
        }
      }
      if (unrecognized.length) {
        payload.issues.push({
          code: "unrecognized_keys",
          keys: unrecognized,
          input,
          inst
        });
      }
      if (!proms.length)
        return payload;
      return Promise.all(proms).then(() => {
        return payload;
      });
    };
  });
  function handleUnionResults(results, final, inst, ctx) {
    for (const result of results) {
      if (result.issues.length === 0) {
        final.value = result.value;
        return final;
      }
    }
    final.issues.push({
      code: "invalid_union",
      input: final.value,
      inst,
      errors: results.map((result) => result.issues.map((iss) => finalizeIssue(iss, ctx, config())))
    });
    return final;
  }
  const $ZodUnion = /* @__PURE__ */ $constructor("$ZodUnion", (inst, def) => {
    $ZodType.init(inst, def);
    defineLazy(inst._zod, "optin", () => def.options.some((o) => o._zod.optin === "optional") ? "optional" : void 0);
    defineLazy(inst._zod, "optout", () => def.options.some((o) => o._zod.optout === "optional") ? "optional" : void 0);
    defineLazy(inst._zod, "values", () => {
      if (def.options.every((o) => o._zod.values)) {
        return new Set(def.options.flatMap((option) => Array.from(option._zod.values)));
      }
      return void 0;
    });
    defineLazy(inst._zod, "pattern", () => {
      if (def.options.every((o) => o._zod.pattern)) {
        const patterns = def.options.map((o) => o._zod.pattern);
        return new RegExp(`^(${patterns.map((p) => cleanRegex(p.source)).join("|")})$`);
      }
      return void 0;
    });
    inst._zod.parse = (payload, ctx) => {
      let async = false;
      const results = [];
      for (const option of def.options) {
        const result = option._zod.run({
          value: payload.value,
          issues: []
        }, ctx);
        if (result instanceof Promise) {
          results.push(result);
          async = true;
        } else {
          if (result.issues.length === 0)
            return result;
          results.push(result);
        }
      }
      if (!async)
        return handleUnionResults(results, payload, inst, ctx);
      return Promise.all(results).then((results2) => {
        return handleUnionResults(results2, payload, inst, ctx);
      });
    };
  });
  const $ZodIntersection = /* @__PURE__ */ $constructor("$ZodIntersection", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.parse = (payload, ctx) => {
      const input = payload.value;
      const left = def.left._zod.run({ value: input, issues: [] }, ctx);
      const right = def.right._zod.run({ value: input, issues: [] }, ctx);
      const async = left instanceof Promise || right instanceof Promise;
      if (async) {
        return Promise.all([left, right]).then(([left2, right2]) => {
          return handleIntersectionResults(payload, left2, right2);
        });
      }
      return handleIntersectionResults(payload, left, right);
    };
  });
  function mergeValues(a, b) {
    if (a === b) {
      return { valid: true, data: a };
    }
    if (a instanceof Date && b instanceof Date && +a === +b) {
      return { valid: true, data: a };
    }
    if (isPlainObject(a) && isPlainObject(b)) {
      const bKeys = Object.keys(b);
      const sharedKeys = Object.keys(a).filter((key) => bKeys.indexOf(key) !== -1);
      const newObj = { ...a, ...b };
      for (const key of sharedKeys) {
        const sharedValue = mergeValues(a[key], b[key]);
        if (!sharedValue.valid) {
          return {
            valid: false,
            mergeErrorPath: [key, ...sharedValue.mergeErrorPath]
          };
        }
        newObj[key] = sharedValue.data;
      }
      return { valid: true, data: newObj };
    }
    if (Array.isArray(a) && Array.isArray(b)) {
      if (a.length !== b.length) {
        return { valid: false, mergeErrorPath: [] };
      }
      const newArray = [];
      for (let index = 0; index < a.length; index++) {
        const itemA = a[index];
        const itemB = b[index];
        const sharedValue = mergeValues(itemA, itemB);
        if (!sharedValue.valid) {
          return {
            valid: false,
            mergeErrorPath: [index, ...sharedValue.mergeErrorPath]
          };
        }
        newArray.push(sharedValue.data);
      }
      return { valid: true, data: newArray };
    }
    return { valid: false, mergeErrorPath: [] };
  }
  function handleIntersectionResults(result, left, right) {
    if (left.issues.length) {
      result.issues.push(...left.issues);
    }
    if (right.issues.length) {
      result.issues.push(...right.issues);
    }
    if (aborted(result))
      return result;
    const merged = mergeValues(left.value, right.value);
    if (!merged.valid) {
      throw new Error(`Unmergable intersection. Error path: ${JSON.stringify(merged.mergeErrorPath)}`);
    }
    result.value = merged.data;
    return result;
  }
  const $ZodEnum = /* @__PURE__ */ $constructor("$ZodEnum", (inst, def) => {
    $ZodType.init(inst, def);
    const values = getEnumValues(def.entries);
    inst._zod.values = new Set(values);
    inst._zod.pattern = new RegExp(`^(${values.filter((k) => propertyKeyTypes.has(typeof k)).map((o) => typeof o === "string" ? escapeRegex(o) : o.toString()).join("|")})$`);
    inst._zod.parse = (payload, _ctx) => {
      const input = payload.value;
      if (inst._zod.values.has(input)) {
        return payload;
      }
      payload.issues.push({
        code: "invalid_value",
        values,
        input,
        inst
      });
      return payload;
    };
  });
  const $ZodTransform = /* @__PURE__ */ $constructor("$ZodTransform", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.parse = (payload, _ctx) => {
      const _out = def.transform(payload.value, payload);
      if (_ctx.async) {
        const output = _out instanceof Promise ? _out : Promise.resolve(_out);
        return output.then((output2) => {
          payload.value = output2;
          return payload;
        });
      }
      if (_out instanceof Promise) {
        throw new $ZodAsyncError();
      }
      payload.value = _out;
      return payload;
    };
  });
  const $ZodOptional = /* @__PURE__ */ $constructor("$ZodOptional", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.optin = "optional";
    inst._zod.optout = "optional";
    defineLazy(inst._zod, "values", () => {
      return def.innerType._zod.values ? /* @__PURE__ */ new Set([...def.innerType._zod.values, void 0]) : void 0;
    });
    defineLazy(inst._zod, "pattern", () => {
      const pattern = def.innerType._zod.pattern;
      return pattern ? new RegExp(`^(${cleanRegex(pattern.source)})?$`) : void 0;
    });
    inst._zod.parse = (payload, ctx) => {
      if (def.innerType._zod.optin === "optional") {
        return def.innerType._zod.run(payload, ctx);
      }
      if (payload.value === void 0) {
        return payload;
      }
      return def.innerType._zod.run(payload, ctx);
    };
  });
  const $ZodNullable = /* @__PURE__ */ $constructor("$ZodNullable", (inst, def) => {
    $ZodType.init(inst, def);
    defineLazy(inst._zod, "optin", () => def.innerType._zod.optin);
    defineLazy(inst._zod, "optout", () => def.innerType._zod.optout);
    defineLazy(inst._zod, "pattern", () => {
      const pattern = def.innerType._zod.pattern;
      return pattern ? new RegExp(`^(${cleanRegex(pattern.source)}|null)$`) : void 0;
    });
    defineLazy(inst._zod, "values", () => {
      return def.innerType._zod.values ? /* @__PURE__ */ new Set([...def.innerType._zod.values, null]) : void 0;
    });
    inst._zod.parse = (payload, ctx) => {
      if (payload.value === null)
        return payload;
      return def.innerType._zod.run(payload, ctx);
    };
  });
  const $ZodDefault = /* @__PURE__ */ $constructor("$ZodDefault", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.optin = "optional";
    defineLazy(inst._zod, "values", () => def.innerType._zod.values);
    inst._zod.parse = (payload, ctx) => {
      if (payload.value === void 0) {
        payload.value = def.defaultValue;
        return payload;
      }
      const result = def.innerType._zod.run(payload, ctx);
      if (result instanceof Promise) {
        return result.then((result2) => handleDefaultResult(result2, def));
      }
      return handleDefaultResult(result, def);
    };
  });
  function handleDefaultResult(payload, def) {
    if (payload.value === void 0) {
      payload.value = def.defaultValue;
    }
    return payload;
  }
  const $ZodPrefault = /* @__PURE__ */ $constructor("$ZodPrefault", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.optin = "optional";
    defineLazy(inst._zod, "values", () => def.innerType._zod.values);
    inst._zod.parse = (payload, ctx) => {
      if (payload.value === void 0) {
        payload.value = def.defaultValue;
      }
      return def.innerType._zod.run(payload, ctx);
    };
  });
  const $ZodNonOptional = /* @__PURE__ */ $constructor("$ZodNonOptional", (inst, def) => {
    $ZodType.init(inst, def);
    defineLazy(inst._zod, "values", () => {
      const v = def.innerType._zod.values;
      return v ? new Set([...v].filter((x) => x !== void 0)) : void 0;
    });
    inst._zod.parse = (payload, ctx) => {
      const result = def.innerType._zod.run(payload, ctx);
      if (result instanceof Promise) {
        return result.then((result2) => handleNonOptionalResult(result2, inst));
      }
      return handleNonOptionalResult(result, inst);
    };
  });
  function handleNonOptionalResult(payload, inst) {
    if (!payload.issues.length && payload.value === void 0) {
      payload.issues.push({
        code: "invalid_type",
        expected: "nonoptional",
        input: payload.value,
        inst
      });
    }
    return payload;
  }
  const $ZodCatch = /* @__PURE__ */ $constructor("$ZodCatch", (inst, def) => {
    $ZodType.init(inst, def);
    inst._zod.optin = "optional";
    defineLazy(inst._zod, "optout", () => def.innerType._zod.optout);
    defineLazy(inst._zod, "values", () => def.innerType._zod.values);
    inst._zod.parse = (payload, ctx) => {
      const result = def.innerType._zod.run(payload, ctx);
      if (result instanceof Promise) {
        return result.then((result2) => {
          payload.value = result2.value;
          if (result2.issues.length) {
            payload.value = def.catchValue({
              ...payload,
              error: {
                issues: result2.issues.map((iss) => finalizeIssue(iss, ctx, config()))
              },
              input: payload.value
            });
            payload.issues = [];
          }
          return payload;
        });
      }
      payload.value = result.value;
      if (result.issues.length) {
        payload.value = def.catchValue({
          ...payload,
          error: {
            issues: result.issues.map((iss) => finalizeIssue(iss, ctx, config()))
          },
          input: payload.value
        });
        payload.issues = [];
      }
      return payload;
    };
  });
  const $ZodPipe = /* @__PURE__ */ $constructor("$ZodPipe", (inst, def) => {
    $ZodType.init(inst, def);
    defineLazy(inst._zod, "values", () => def.in._zod.values);
    defineLazy(inst._zod, "optin", () => def.in._zod.optin);
    defineLazy(inst._zod, "optout", () => def.out._zod.optout);
    defineLazy(inst._zod, "propValues", () => def.in._zod.propValues);
    inst._zod.parse = (payload, ctx) => {
      const left = def.in._zod.run(payload, ctx);
      if (left instanceof Promise) {
        return left.then((left2) => handlePipeResult(left2, def, ctx));
      }
      return handlePipeResult(left, def, ctx);
    };
  });
  function handlePipeResult(left, def, ctx) {
    if (aborted(left)) {
      return left;
    }
    return def.out._zod.run({ value: left.value, issues: left.issues }, ctx);
  }
  const $ZodReadonly = /* @__PURE__ */ $constructor("$ZodReadonly", (inst, def) => {
    $ZodType.init(inst, def);
    defineLazy(inst._zod, "propValues", () => def.innerType._zod.propValues);
    defineLazy(inst._zod, "values", () => def.innerType._zod.values);
    defineLazy(inst._zod, "optin", () => def.innerType._zod.optin);
    defineLazy(inst._zod, "optout", () => def.innerType._zod.optout);
    inst._zod.parse = (payload, ctx) => {
      const result = def.innerType._zod.run(payload, ctx);
      if (result instanceof Promise) {
        return result.then(handleReadonlyResult);
      }
      return handleReadonlyResult(result);
    };
  });
  function handleReadonlyResult(payload) {
    payload.value = Object.freeze(payload.value);
    return payload;
  }
  const $ZodCustom = /* @__PURE__ */ $constructor("$ZodCustom", (inst, def) => {
    $ZodCheck.init(inst, def);
    $ZodType.init(inst, def);
    inst._zod.parse = (payload, _) => {
      return payload;
    };
    inst._zod.check = (payload) => {
      const input = payload.value;
      const r = def.fn(input);
      if (r instanceof Promise) {
        return r.then((r2) => handleRefineResult(r2, payload, input, inst));
      }
      handleRefineResult(r, payload, input, inst);
      return;
    };
  });
  function handleRefineResult(result, payload, input, inst) {
    if (!result) {
      const _iss = {
        code: "custom",
        input,
        inst,
        // incorporates params.error into issue reporting
        path: [...inst._zod.def.path ?? []],
        // incorporates params.error into issue reporting
        continue: !inst._zod.def.abort
        // params: inst._zod.def.params,
      };
      if (inst._zod.def.params)
        _iss.params = inst._zod.def.params;
      payload.issues.push(issue(_iss));
    }
  }
  class $ZodRegistry {
    constructor() {
      this._map = /* @__PURE__ */ new Map();
      this._idmap = /* @__PURE__ */ new Map();
    }
    add(schema, ..._meta) {
      const meta = _meta[0];
      this._map.set(schema, meta);
      if (meta && typeof meta === "object" && "id" in meta) {
        if (this._idmap.has(meta.id)) {
          throw new Error(`ID ${meta.id} already exists in the registry`);
        }
        this._idmap.set(meta.id, schema);
      }
      return this;
    }
    clear() {
      this._map = /* @__PURE__ */ new Map();
      this._idmap = /* @__PURE__ */ new Map();
      return this;
    }
    remove(schema) {
      const meta = this._map.get(schema);
      if (meta && typeof meta === "object" && "id" in meta) {
        this._idmap.delete(meta.id);
      }
      this._map.delete(schema);
      return this;
    }
    get(schema) {
      const p = schema._zod.parent;
      if (p) {
        const pm = { ...this.get(p) ?? {} };
        delete pm.id;
        return { ...pm, ...this._map.get(schema) };
      }
      return this._map.get(schema);
    }
    has(schema) {
      return this._map.has(schema);
    }
  }
  function registry() {
    return new $ZodRegistry();
  }
  const globalRegistry = /* @__PURE__ */ registry();
  function _string(Class, params) {
    return new Class({
      type: "string",
      ...normalizeParams(params)
    });
  }
  function _coercedString(Class, params) {
    return new Class({
      type: "string",
      coerce: true,
      ...normalizeParams(params)
    });
  }
  function _email(Class, params) {
    return new Class({
      type: "string",
      format: "email",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _guid(Class, params) {
    return new Class({
      type: "string",
      format: "guid",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _uuid(Class, params) {
    return new Class({
      type: "string",
      format: "uuid",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _uuidv4(Class, params) {
    return new Class({
      type: "string",
      format: "uuid",
      check: "string_format",
      abort: false,
      version: "v4",
      ...normalizeParams(params)
    });
  }
  function _uuidv6(Class, params) {
    return new Class({
      type: "string",
      format: "uuid",
      check: "string_format",
      abort: false,
      version: "v6",
      ...normalizeParams(params)
    });
  }
  function _uuidv7(Class, params) {
    return new Class({
      type: "string",
      format: "uuid",
      check: "string_format",
      abort: false,
      version: "v7",
      ...normalizeParams(params)
    });
  }
  function _url(Class, params) {
    return new Class({
      type: "string",
      format: "url",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _emoji(Class, params) {
    return new Class({
      type: "string",
      format: "emoji",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _nanoid(Class, params) {
    return new Class({
      type: "string",
      format: "nanoid",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _cuid(Class, params) {
    return new Class({
      type: "string",
      format: "cuid",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _cuid2(Class, params) {
    return new Class({
      type: "string",
      format: "cuid2",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _ulid(Class, params) {
    return new Class({
      type: "string",
      format: "ulid",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _xid(Class, params) {
    return new Class({
      type: "string",
      format: "xid",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _ksuid(Class, params) {
    return new Class({
      type: "string",
      format: "ksuid",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _ipv4(Class, params) {
    return new Class({
      type: "string",
      format: "ipv4",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _ipv6(Class, params) {
    return new Class({
      type: "string",
      format: "ipv6",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _cidrv4(Class, params) {
    return new Class({
      type: "string",
      format: "cidrv4",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _cidrv6(Class, params) {
    return new Class({
      type: "string",
      format: "cidrv6",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _base64(Class, params) {
    return new Class({
      type: "string",
      format: "base64",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _base64url(Class, params) {
    return new Class({
      type: "string",
      format: "base64url",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _e164(Class, params) {
    return new Class({
      type: "string",
      format: "e164",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _jwt(Class, params) {
    return new Class({
      type: "string",
      format: "jwt",
      check: "string_format",
      abort: false,
      ...normalizeParams(params)
    });
  }
  function _isoDateTime(Class, params) {
    return new Class({
      type: "string",
      format: "datetime",
      check: "string_format",
      offset: false,
      local: false,
      precision: null,
      ...normalizeParams(params)
    });
  }
  function _isoDate(Class, params) {
    return new Class({
      type: "string",
      format: "date",
      check: "string_format",
      ...normalizeParams(params)
    });
  }
  function _isoTime(Class, params) {
    return new Class({
      type: "string",
      format: "time",
      check: "string_format",
      precision: null,
      ...normalizeParams(params)
    });
  }
  function _isoDuration(Class, params) {
    return new Class({
      type: "string",
      format: "duration",
      check: "string_format",
      ...normalizeParams(params)
    });
  }
  function _unknown(Class) {
    return new Class({
      type: "unknown"
    });
  }
  function _never(Class, params) {
    return new Class({
      type: "never",
      ...normalizeParams(params)
    });
  }
  function _date(Class, params) {
    return new Class({
      type: "date",
      ...normalizeParams(params)
    });
  }
  function _lte(value, params) {
    return new $ZodCheckLessThan({
      check: "less_than",
      ...normalizeParams(params),
      value,
      inclusive: true
    });
  }
  function _gte(value, params) {
    return new $ZodCheckGreaterThan({
      check: "greater_than",
      ...normalizeParams(params),
      value,
      inclusive: true
    });
  }
  function _maxLength(maximum, params) {
    const ch = new $ZodCheckMaxLength({
      check: "max_length",
      ...normalizeParams(params),
      maximum
    });
    return ch;
  }
  function _minLength(minimum, params) {
    return new $ZodCheckMinLength({
      check: "min_length",
      ...normalizeParams(params),
      minimum
    });
  }
  function _length(length, params) {
    return new $ZodCheckLengthEquals({
      check: "length_equals",
      ...normalizeParams(params),
      length
    });
  }
  function _regex(pattern, params) {
    return new $ZodCheckRegex({
      check: "string_format",
      format: "regex",
      ...normalizeParams(params),
      pattern
    });
  }
  function _lowercase(params) {
    return new $ZodCheckLowerCase({
      check: "string_format",
      format: "lowercase",
      ...normalizeParams(params)
    });
  }
  function _uppercase(params) {
    return new $ZodCheckUpperCase({
      check: "string_format",
      format: "uppercase",
      ...normalizeParams(params)
    });
  }
  function _includes(includes, params) {
    return new $ZodCheckIncludes({
      check: "string_format",
      format: "includes",
      ...normalizeParams(params),
      includes
    });
  }
  function _startsWith(prefix, params) {
    return new $ZodCheckStartsWith({
      check: "string_format",
      format: "starts_with",
      ...normalizeParams(params),
      prefix
    });
  }
  function _endsWith(suffix, params) {
    return new $ZodCheckEndsWith({
      check: "string_format",
      format: "ends_with",
      ...normalizeParams(params),
      suffix
    });
  }
  function _overwrite(tx) {
    return new $ZodCheckOverwrite({
      check: "overwrite",
      tx
    });
  }
  function _normalize(form) {
    return _overwrite((input) => input.normalize(form));
  }
  function _trim() {
    return _overwrite((input) => input.trim());
  }
  function _toLowerCase() {
    return _overwrite((input) => input.toLowerCase());
  }
  function _toUpperCase() {
    return _overwrite((input) => input.toUpperCase());
  }
  function _array(Class, element, params) {
    return new Class({
      type: "array",
      element,
      // get element() {
      //   return element;
      // },
      ...normalizeParams(params)
    });
  }
  function _refine(Class, fn, _params) {
    const schema = new Class({
      type: "custom",
      check: "custom",
      fn,
      ...normalizeParams(_params)
    });
    return schema;
  }
  const ZodISODateTime = /* @__PURE__ */ $constructor("ZodISODateTime", (inst, def) => {
    $ZodISODateTime.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  function datetime(params) {
    return _isoDateTime(ZodISODateTime, params);
  }
  const ZodISODate = /* @__PURE__ */ $constructor("ZodISODate", (inst, def) => {
    $ZodISODate.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  function date$1(params) {
    return _isoDate(ZodISODate, params);
  }
  const ZodISOTime = /* @__PURE__ */ $constructor("ZodISOTime", (inst, def) => {
    $ZodISOTime.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  function time(params) {
    return _isoTime(ZodISOTime, params);
  }
  const ZodISODuration = /* @__PURE__ */ $constructor("ZodISODuration", (inst, def) => {
    $ZodISODuration.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  function duration(params) {
    return _isoDuration(ZodISODuration, params);
  }
  const initializer = (inst, issues) => {
    $ZodError.init(inst, issues);
    inst.name = "ZodError";
    Object.defineProperties(inst, {
      format: {
        value: (mapper) => formatError(inst, mapper)
        // enumerable: false,
      },
      flatten: {
        value: (mapper) => flattenError(inst, mapper)
        // enumerable: false,
      },
      addIssue: {
        value: (issue2) => inst.issues.push(issue2)
        // enumerable: false,
      },
      addIssues: {
        value: (issues2) => inst.issues.push(...issues2)
        // enumerable: false,
      },
      isEmpty: {
        get() {
          return inst.issues.length === 0;
        }
        // enumerable: false,
      }
    });
  };
  const ZodRealError = $constructor("ZodError", initializer, {
    Parent: Error
  });
  const parse = /* @__PURE__ */ _parse(ZodRealError);
  const parseAsync = /* @__PURE__ */ _parseAsync(ZodRealError);
  const safeParse = /* @__PURE__ */ _safeParse(ZodRealError);
  const safeParseAsync = /* @__PURE__ */ _safeParseAsync(ZodRealError);
  const ZodType = /* @__PURE__ */ $constructor("ZodType", (inst, def) => {
    $ZodType.init(inst, def);
    inst.def = def;
    Object.defineProperty(inst, "_def", { value: def });
    inst.check = (...checks) => {
      return inst.clone(
        {
          ...def,
          checks: [
            ...def.checks ?? [],
            ...checks.map((ch) => typeof ch === "function" ? { _zod: { check: ch, def: { check: "custom" }, onattach: [] } } : ch)
          ]
        }
        // { parent: true }
      );
    };
    inst.clone = (def2, params) => clone(inst, def2, params);
    inst.brand = () => inst;
    inst.register = (reg, meta) => {
      reg.add(inst, meta);
      return inst;
    };
    inst.parse = (data, params) => parse(inst, data, params, { callee: inst.parse });
    inst.safeParse = (data, params) => safeParse(inst, data, params);
    inst.parseAsync = async (data, params) => parseAsync(inst, data, params, { callee: inst.parseAsync });
    inst.safeParseAsync = async (data, params) => safeParseAsync(inst, data, params);
    inst.spa = inst.safeParseAsync;
    inst.refine = (check2, params) => inst.check(refine(check2, params));
    inst.superRefine = (refinement) => inst.check(superRefine(refinement));
    inst.overwrite = (fn) => inst.check(_overwrite(fn));
    inst.optional = () => optional(inst);
    inst.nullable = () => nullable(inst);
    inst.nullish = () => optional(nullable(inst));
    inst.nonoptional = (params) => nonoptional(inst, params);
    inst.array = () => array(inst);
    inst.or = (arg) => union([inst, arg]);
    inst.and = (arg) => intersection(inst, arg);
    inst.transform = (tx) => pipe(inst, transform(tx));
    inst.default = (def2) => _default(inst, def2);
    inst.prefault = (def2) => prefault(inst, def2);
    inst.catch = (params) => _catch(inst, params);
    inst.pipe = (target) => pipe(inst, target);
    inst.readonly = () => readonly(inst);
    inst.describe = (description) => {
      const cl = inst.clone();
      globalRegistry.add(cl, { description });
      return cl;
    };
    Object.defineProperty(inst, "description", {
      get() {
        return globalRegistry.get(inst)?.description;
      },
      configurable: true
    });
    inst.meta = (...args) => {
      if (args.length === 0) {
        return globalRegistry.get(inst);
      }
      const cl = inst.clone();
      globalRegistry.add(cl, args[0]);
      return cl;
    };
    inst.isOptional = () => inst.safeParse(void 0).success;
    inst.isNullable = () => inst.safeParse(null).success;
    return inst;
  });
  const _ZodString = /* @__PURE__ */ $constructor("_ZodString", (inst, def) => {
    $ZodString.init(inst, def);
    ZodType.init(inst, def);
    const bag = inst._zod.bag;
    inst.format = bag.format ?? null;
    inst.minLength = bag.minimum ?? null;
    inst.maxLength = bag.maximum ?? null;
    inst.regex = (...args) => inst.check(_regex(...args));
    inst.includes = (...args) => inst.check(_includes(...args));
    inst.startsWith = (...args) => inst.check(_startsWith(...args));
    inst.endsWith = (...args) => inst.check(_endsWith(...args));
    inst.min = (...args) => inst.check(_minLength(...args));
    inst.max = (...args) => inst.check(_maxLength(...args));
    inst.length = (...args) => inst.check(_length(...args));
    inst.nonempty = (...args) => inst.check(_minLength(1, ...args));
    inst.lowercase = (params) => inst.check(_lowercase(params));
    inst.uppercase = (params) => inst.check(_uppercase(params));
    inst.trim = () => inst.check(_trim());
    inst.normalize = (...args) => inst.check(_normalize(...args));
    inst.toLowerCase = () => inst.check(_toLowerCase());
    inst.toUpperCase = () => inst.check(_toUpperCase());
  });
  const ZodString = /* @__PURE__ */ $constructor("ZodString", (inst, def) => {
    $ZodString.init(inst, def);
    _ZodString.init(inst, def);
    inst.email = (params) => inst.check(_email(ZodEmail, params));
    inst.url = (params) => inst.check(_url(ZodURL, params));
    inst.jwt = (params) => inst.check(_jwt(ZodJWT, params));
    inst.emoji = (params) => inst.check(_emoji(ZodEmoji, params));
    inst.guid = (params) => inst.check(_guid(ZodGUID, params));
    inst.uuid = (params) => inst.check(_uuid(ZodUUID, params));
    inst.uuidv4 = (params) => inst.check(_uuidv4(ZodUUID, params));
    inst.uuidv6 = (params) => inst.check(_uuidv6(ZodUUID, params));
    inst.uuidv7 = (params) => inst.check(_uuidv7(ZodUUID, params));
    inst.nanoid = (params) => inst.check(_nanoid(ZodNanoID, params));
    inst.guid = (params) => inst.check(_guid(ZodGUID, params));
    inst.cuid = (params) => inst.check(_cuid(ZodCUID, params));
    inst.cuid2 = (params) => inst.check(_cuid2(ZodCUID2, params));
    inst.ulid = (params) => inst.check(_ulid(ZodULID, params));
    inst.base64 = (params) => inst.check(_base64(ZodBase64, params));
    inst.base64url = (params) => inst.check(_base64url(ZodBase64URL, params));
    inst.xid = (params) => inst.check(_xid(ZodXID, params));
    inst.ksuid = (params) => inst.check(_ksuid(ZodKSUID, params));
    inst.ipv4 = (params) => inst.check(_ipv4(ZodIPv4, params));
    inst.ipv6 = (params) => inst.check(_ipv6(ZodIPv6, params));
    inst.cidrv4 = (params) => inst.check(_cidrv4(ZodCIDRv4, params));
    inst.cidrv6 = (params) => inst.check(_cidrv6(ZodCIDRv6, params));
    inst.e164 = (params) => inst.check(_e164(ZodE164, params));
    inst.datetime = (params) => inst.check(datetime(params));
    inst.date = (params) => inst.check(date$1(params));
    inst.time = (params) => inst.check(time(params));
    inst.duration = (params) => inst.check(duration(params));
  });
  function string$1(params) {
    return _string(ZodString, params);
  }
  const ZodStringFormat = /* @__PURE__ */ $constructor("ZodStringFormat", (inst, def) => {
    $ZodStringFormat.init(inst, def);
    _ZodString.init(inst, def);
  });
  const ZodEmail = /* @__PURE__ */ $constructor("ZodEmail", (inst, def) => {
    $ZodEmail.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodGUID = /* @__PURE__ */ $constructor("ZodGUID", (inst, def) => {
    $ZodGUID.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodUUID = /* @__PURE__ */ $constructor("ZodUUID", (inst, def) => {
    $ZodUUID.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodURL = /* @__PURE__ */ $constructor("ZodURL", (inst, def) => {
    $ZodURL.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodEmoji = /* @__PURE__ */ $constructor("ZodEmoji", (inst, def) => {
    $ZodEmoji.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodNanoID = /* @__PURE__ */ $constructor("ZodNanoID", (inst, def) => {
    $ZodNanoID.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodCUID = /* @__PURE__ */ $constructor("ZodCUID", (inst, def) => {
    $ZodCUID.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodCUID2 = /* @__PURE__ */ $constructor("ZodCUID2", (inst, def) => {
    $ZodCUID2.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodULID = /* @__PURE__ */ $constructor("ZodULID", (inst, def) => {
    $ZodULID.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodXID = /* @__PURE__ */ $constructor("ZodXID", (inst, def) => {
    $ZodXID.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodKSUID = /* @__PURE__ */ $constructor("ZodKSUID", (inst, def) => {
    $ZodKSUID.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodIPv4 = /* @__PURE__ */ $constructor("ZodIPv4", (inst, def) => {
    $ZodIPv4.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodIPv6 = /* @__PURE__ */ $constructor("ZodIPv6", (inst, def) => {
    $ZodIPv6.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodCIDRv4 = /* @__PURE__ */ $constructor("ZodCIDRv4", (inst, def) => {
    $ZodCIDRv4.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodCIDRv6 = /* @__PURE__ */ $constructor("ZodCIDRv6", (inst, def) => {
    $ZodCIDRv6.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodBase64 = /* @__PURE__ */ $constructor("ZodBase64", (inst, def) => {
    $ZodBase64.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodBase64URL = /* @__PURE__ */ $constructor("ZodBase64URL", (inst, def) => {
    $ZodBase64URL.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodE164 = /* @__PURE__ */ $constructor("ZodE164", (inst, def) => {
    $ZodE164.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodJWT = /* @__PURE__ */ $constructor("ZodJWT", (inst, def) => {
    $ZodJWT.init(inst, def);
    ZodStringFormat.init(inst, def);
  });
  const ZodUnknown = /* @__PURE__ */ $constructor("ZodUnknown", (inst, def) => {
    $ZodUnknown.init(inst, def);
    ZodType.init(inst, def);
  });
  function unknown() {
    return _unknown(ZodUnknown);
  }
  const ZodNever = /* @__PURE__ */ $constructor("ZodNever", (inst, def) => {
    $ZodNever.init(inst, def);
    ZodType.init(inst, def);
  });
  function never(params) {
    return _never(ZodNever, params);
  }
  const ZodDate = /* @__PURE__ */ $constructor("ZodDate", (inst, def) => {
    $ZodDate.init(inst, def);
    ZodType.init(inst, def);
    inst.min = (value, params) => inst.check(_gte(value, params));
    inst.max = (value, params) => inst.check(_lte(value, params));
    const c = inst._zod.bag;
    inst.minDate = c.minimum ? new Date(c.minimum) : null;
    inst.maxDate = c.maximum ? new Date(c.maximum) : null;
  });
  function date(params) {
    return _date(ZodDate, params);
  }
  const ZodArray = /* @__PURE__ */ $constructor("ZodArray", (inst, def) => {
    $ZodArray.init(inst, def);
    ZodType.init(inst, def);
    inst.element = def.element;
    inst.min = (minLength, params) => inst.check(_minLength(minLength, params));
    inst.nonempty = (params) => inst.check(_minLength(1, params));
    inst.max = (maxLength, params) => inst.check(_maxLength(maxLength, params));
    inst.length = (len, params) => inst.check(_length(len, params));
    inst.unwrap = () => inst.element;
  });
  function array(element, params) {
    return _array(ZodArray, element, params);
  }
  const ZodObject = /* @__PURE__ */ $constructor("ZodObject", (inst, def) => {
    $ZodObject.init(inst, def);
    ZodType.init(inst, def);
    defineLazy(inst, "shape", () => def.shape);
    inst.keyof = () => _enum(Object.keys(inst._zod.def.shape));
    inst.catchall = (catchall) => inst.clone({ ...inst._zod.def, catchall });
    inst.passthrough = () => inst.clone({ ...inst._zod.def, catchall: unknown() });
    inst.loose = () => inst.clone({ ...inst._zod.def, catchall: unknown() });
    inst.strict = () => inst.clone({ ...inst._zod.def, catchall: never() });
    inst.strip = () => inst.clone({ ...inst._zod.def, catchall: void 0 });
    inst.extend = (incoming) => {
      return extend(inst, incoming);
    };
    inst.merge = (other) => merge(inst, other);
    inst.pick = (mask) => pick(inst, mask);
    inst.omit = (mask) => omit(inst, mask);
    inst.partial = (...args) => partial(ZodOptional, inst, args[0]);
    inst.required = (...args) => required(ZodNonOptional, inst, args[0]);
  });
  function object(shape, params) {
    const def = {
      type: "object",
      get shape() {
        assignProp(this, "shape", { ...shape });
        return this.shape;
      },
      ...normalizeParams(params)
    };
    return new ZodObject(def);
  }
  const ZodUnion = /* @__PURE__ */ $constructor("ZodUnion", (inst, def) => {
    $ZodUnion.init(inst, def);
    ZodType.init(inst, def);
    inst.options = def.options;
  });
  function union(options, params) {
    return new ZodUnion({
      type: "union",
      options,
      ...normalizeParams(params)
    });
  }
  const ZodIntersection = /* @__PURE__ */ $constructor("ZodIntersection", (inst, def) => {
    $ZodIntersection.init(inst, def);
    ZodType.init(inst, def);
  });
  function intersection(left, right) {
    return new ZodIntersection({
      type: "intersection",
      left,
      right
    });
  }
  const ZodEnum = /* @__PURE__ */ $constructor("ZodEnum", (inst, def) => {
    $ZodEnum.init(inst, def);
    ZodType.init(inst, def);
    inst.enum = def.entries;
    inst.options = Object.values(def.entries);
    const keys = new Set(Object.keys(def.entries));
    inst.extract = (values, params) => {
      const newEntries = {};
      for (const value of values) {
        if (keys.has(value)) {
          newEntries[value] = def.entries[value];
        } else
          throw new Error(`Key ${value} not found in enum`);
      }
      return new ZodEnum({
        ...def,
        checks: [],
        ...normalizeParams(params),
        entries: newEntries
      });
    };
    inst.exclude = (values, params) => {
      const newEntries = { ...def.entries };
      for (const value of values) {
        if (keys.has(value)) {
          delete newEntries[value];
        } else
          throw new Error(`Key ${value} not found in enum`);
      }
      return new ZodEnum({
        ...def,
        checks: [],
        ...normalizeParams(params),
        entries: newEntries
      });
    };
  });
  function _enum(values, params) {
    const entries = Array.isArray(values) ? Object.fromEntries(values.map((v) => [v, v])) : values;
    return new ZodEnum({
      type: "enum",
      entries,
      ...normalizeParams(params)
    });
  }
  const ZodTransform = /* @__PURE__ */ $constructor("ZodTransform", (inst, def) => {
    $ZodTransform.init(inst, def);
    ZodType.init(inst, def);
    inst._zod.parse = (payload, _ctx) => {
      payload.addIssue = (issue$1) => {
        if (typeof issue$1 === "string") {
          payload.issues.push(issue(issue$1, payload.value, def));
        } else {
          const _issue = issue$1;
          if (_issue.fatal)
            _issue.continue = false;
          _issue.code ?? (_issue.code = "custom");
          _issue.input ?? (_issue.input = payload.value);
          _issue.inst ?? (_issue.inst = inst);
          _issue.continue ?? (_issue.continue = true);
          payload.issues.push(issue(_issue));
        }
      };
      const output = def.transform(payload.value, payload);
      if (output instanceof Promise) {
        return output.then((output2) => {
          payload.value = output2;
          return payload;
        });
      }
      payload.value = output;
      return payload;
    };
  });
  function transform(fn) {
    return new ZodTransform({
      type: "transform",
      transform: fn
    });
  }
  const ZodOptional = /* @__PURE__ */ $constructor("ZodOptional", (inst, def) => {
    $ZodOptional.init(inst, def);
    ZodType.init(inst, def);
    inst.unwrap = () => inst._zod.def.innerType;
  });
  function optional(innerType) {
    return new ZodOptional({
      type: "optional",
      innerType
    });
  }
  const ZodNullable = /* @__PURE__ */ $constructor("ZodNullable", (inst, def) => {
    $ZodNullable.init(inst, def);
    ZodType.init(inst, def);
    inst.unwrap = () => inst._zod.def.innerType;
  });
  function nullable(innerType) {
    return new ZodNullable({
      type: "nullable",
      innerType
    });
  }
  const ZodDefault = /* @__PURE__ */ $constructor("ZodDefault", (inst, def) => {
    $ZodDefault.init(inst, def);
    ZodType.init(inst, def);
    inst.unwrap = () => inst._zod.def.innerType;
    inst.removeDefault = inst.unwrap;
  });
  function _default(innerType, defaultValue) {
    return new ZodDefault({
      type: "default",
      innerType,
      get defaultValue() {
        return typeof defaultValue === "function" ? defaultValue() : defaultValue;
      }
    });
  }
  const ZodPrefault = /* @__PURE__ */ $constructor("ZodPrefault", (inst, def) => {
    $ZodPrefault.init(inst, def);
    ZodType.init(inst, def);
    inst.unwrap = () => inst._zod.def.innerType;
  });
  function prefault(innerType, defaultValue) {
    return new ZodPrefault({
      type: "prefault",
      innerType,
      get defaultValue() {
        return typeof defaultValue === "function" ? defaultValue() : defaultValue;
      }
    });
  }
  const ZodNonOptional = /* @__PURE__ */ $constructor("ZodNonOptional", (inst, def) => {
    $ZodNonOptional.init(inst, def);
    ZodType.init(inst, def);
    inst.unwrap = () => inst._zod.def.innerType;
  });
  function nonoptional(innerType, params) {
    return new ZodNonOptional({
      type: "nonoptional",
      innerType,
      ...normalizeParams(params)
    });
  }
  const ZodCatch = /* @__PURE__ */ $constructor("ZodCatch", (inst, def) => {
    $ZodCatch.init(inst, def);
    ZodType.init(inst, def);
    inst.unwrap = () => inst._zod.def.innerType;
    inst.removeCatch = inst.unwrap;
  });
  function _catch(innerType, catchValue) {
    return new ZodCatch({
      type: "catch",
      innerType,
      catchValue: typeof catchValue === "function" ? catchValue : () => catchValue
    });
  }
  const ZodPipe = /* @__PURE__ */ $constructor("ZodPipe", (inst, def) => {
    $ZodPipe.init(inst, def);
    ZodType.init(inst, def);
    inst.in = def.in;
    inst.out = def.out;
  });
  function pipe(in_, out) {
    return new ZodPipe({
      type: "pipe",
      in: in_,
      out
      // ...util.normalizeParams(params),
    });
  }
  const ZodReadonly = /* @__PURE__ */ $constructor("ZodReadonly", (inst, def) => {
    $ZodReadonly.init(inst, def);
    ZodType.init(inst, def);
  });
  function readonly(innerType) {
    return new ZodReadonly({
      type: "readonly",
      innerType
    });
  }
  const ZodCustom = /* @__PURE__ */ $constructor("ZodCustom", (inst, def) => {
    $ZodCustom.init(inst, def);
    ZodType.init(inst, def);
  });
  function check(fn) {
    const ch = new $ZodCheck({
      check: "custom"
      // ...util.normalizeParams(params),
    });
    ch._zod.check = fn;
    return ch;
  }
  function refine(fn, _params = {}) {
    return _refine(ZodCustom, fn, _params);
  }
  function superRefine(fn) {
    const ch = check((payload) => {
      payload.addIssue = (issue$1) => {
        if (typeof issue$1 === "string") {
          payload.issues.push(issue(issue$1, payload.value, ch._zod.def));
        } else {
          const _issue = issue$1;
          if (_issue.fatal)
            _issue.continue = false;
          _issue.code ?? (_issue.code = "custom");
          _issue.input ?? (_issue.input = payload.value);
          _issue.inst ?? (_issue.inst = ch);
          _issue.continue ?? (_issue.continue = !ch._zod.def.abort);
          payload.issues.push(issue(_issue));
        }
      };
      return fn(payload.value, payload);
    });
    return ch;
  }
  function string(params) {
    return _coercedString(ZodString, params);
  }
  const IdSchema = string$1();
  const NameSchema = string$1();
  const timestampTransformer = string$1().or(date()).transform((val) => {
    if (val instanceof Date) return val;
    return new Date(val);
  });
  const SQLRowMetaDataSchema = object({
    id: string(),
    created_at: timestampTransformer,
    updated_at: timestampTransformer
  });
  const PinTypeSerializer = _enum(["PWR", "GND", "NORMAL"]).default("NORMAL");
  const PinSerializer = object({
    id: IdSchema,
    name: NameSchema,
    pinType: PinTypeSerializer
  });
  const NetTypeSchema = _enum(["PWR", "GND", "NORMAL"]).default("NORMAL");
  const ComponentSchema = object({
    id: IdSchema,
    name: NameSchema,
    pins: array(PinSerializer)
  });
  const NetSchema = object({
    id: IdSchema,
    name: NameSchema,
    netType: NetTypeSchema
  });
  const ConnectionSchema = object({
    netId: IdSchema,
    pinId: IdSchema
  });
  object({
    connections: array(ConnectionSchema),
    components: array(ComponentSchema),
    nets: array(NetSchema)
  });
  function createOptimizedNetList(netList) {
    const nets = Object.fromEntries(
      netList.nets.map(
        (net) => [net.id, net]
      )
    );
    const components = Object.fromEntries(
      netList.components.map(
        (component) => [component.id, component]
      )
    );
    const pins = Object.fromEntries(
      netList.components.flatMap(
        ({ pins: pins2 }) => pins2.map((pin) => [pin.id, pin])
      )
    );
    const pinIdsByNetId = {};
    for (const connection of netList.connections) {
      pinIdsByNetId[connection.netId] = Object.hasOwn(pinIdsByNetId, connection.netId) ? pinIdsByNetId[connection.netId].concat([connection.pinId]) : [connection.pinId];
    }
    return {
      connections: netList.connections,
      nets,
      components,
      pins,
      pinIdsByNetId
    };
  }
  const NetListRowSchema = SQLRowMetaDataSchema.extend(
    object(
      {
        name: string$1(),
        netlist: object({}).loose()
      }
    ).shape
  );
  array(
    NetListRowSchema
  );
  self.onmessage = (e) => {
    const netList = e.data;
    const optimizedNetList = createOptimizedNetList(netList);
    const render = createNetListRender(optimizedNetList);
    self.postMessage(render);
  };
})();
//# sourceMappingURL=NetListWorker-Dyt-DpsL.js.map
