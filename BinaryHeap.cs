using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class Heap
    {
        private Vertex[] heapArray;
        private int maxSize;
        public int currentSize;
        public Heap(int maxHeapSize)
        {
            maxSize = maxHeapSize;
            currentSize = 0;
            heapArray = new Vertex[maxSize];
        }
        public bool IsEmpty()
        { return currentSize == 0; }

        public bool Insert(Vertex value)
        {
            if (currentSize == maxSize)
                return false;
            Vertex newVertex = value;
            heapArray[currentSize] = newVertex;
            CascadeUp(currentSize++);
            return true;
        }
        public void CascadeUp(int index)
        {
            int parent = (index - 1) / 2;
            Vertex bottom = heapArray[index];
            while (index > 0 && Comparer(heapArray[parent], bottom)>0)
            {
                heapArray[index] = heapArray[parent];
                index = parent;
                parent = (parent - 1) / 2;
            }
            heapArray[index] = bottom;
        }
        public Vertex Remove() // Remove maximum value Vertex
        {
            Vertex root = heapArray[0];
            heapArray[0] = heapArray[--currentSize];
            CascadeDown(0);
            return root;
        }
        public void CascadeDown(int index)
        {
            int largerChild;
            Vertex top = heapArray[index];
            while (index < currentSize / 2)
            {
                int leftChild = 2 * index + 1;
                int rightChild = leftChild + 1;
                if (rightChild < currentSize && Comparer(heapArray[leftChild],heapArray[rightChild])>0)
                    largerChild = rightChild;
                else
                    largerChild = leftChild;
                if (Comparer(heapArray[largerChild],top)>=0) 
                    break;
                heapArray[index] = heapArray[largerChild];
                index = largerChild;
            }
            heapArray[index] = top;
        }
       /* public bool HeapIncreaseDecreaseKey(int index, int newValue)
        {
            if (index < 0 || index >= currentSize)
                return false;
            int oldValue = heapArray[index].getvalue();
            heapArray[index].setvalue(newValue);
            if (oldValue < newValue)
                CascadeUp(index);
            else
                CascadeDown(index);
            return true;
        }*/
       /* public void DisplayHeap()
        {
            Console.WriteLine();
            Console.Write("Elements of the Heap Array are : ");
            for (int m = 0; m < currentSize; m++)
                if (heapArray[m] != null)
                    Console.Write(heapArray[m].getvalue() + " ");
                else
                    Console.Write("-- ");
            Console.WriteLine();
            int emptyLeaf = 32;
            int itemsPerRow = 1;
            int column = 0;
            int j = 0;
            String separator = "...............................";
            Console.WriteLine(separator + separator);
            while (currentSize > 0)
            {
                if (column == 0)
                    for (int k = 0; k < emptyLeaf; k++)
                        Console.Write(' ');
                Console.Write(heapArray[j].getvalue());

                if (++j == currentSize)
                    break;
                if (++column == itemsPerRow)
                {
                    emptyLeaf /= 2;
                    itemsPerRow *= 2;
                    column = 0;
                    Console.WriteLine();
                }
                else
                    for (int k = 0; k < emptyLeaf * 2 - 2; k++)
                        Console.Write(' ');
            }
            Console.WriteLine("\n" + separator + separator);
        }
        */
        public int Comparer(Vertex v1, Vertex v2)
        {
            if (v1.h == v2.h)
            {
                if (v1.g == v2.g)
                {
                    /*if (v1.cost > v2.cost)
                        return 1;
                    if (v1.cost < v2.cost)
                        return -1;*/

                    return 0;
                }
                if (v1.g > v2.g)
                    return 1;
                else
                    return -1;



            }
            if (v1.h > v2.h) return 1;
            return -1;

        }
    }
}
