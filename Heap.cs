using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

namespace Planning
{
    class Heap<D>
    {
        private List<Pair<D>> m_lHeap;
        private Dictionary<D, int> m_dLocation;

        public Heap()
        {
            m_lHeap = new List<Pair<D>>();
            m_dLocation = new Dictionary<D, int>();
        }

        public void Insert(D data, double priority)
        {
            m_lHeap.Add(new Pair<D>(data, priority));
            m_dLocation[data] = m_lHeap.Count - 1;
            BubbleUp(m_lHeap.Count - 1);
            //Debug.Assert(ValidateHeap());

        }
        public void IncreasePriority(D data, double priority)
        {
            if (!m_dLocation.ContainsKey(data))
                Insert(data, priority);
            else
            {
                int idx = m_dLocation[data];
                if (m_lHeap[idx].Priority < priority)
                {
                    m_lHeap[idx].Priority = priority;
                    BubbleUp(idx);
                }
            }
            //Debug.Assert(ValidateHeap());

        }
        public D ExtractMax()
        {
            D data = m_lHeap[0].Data;
            Swap(0, m_lHeap.Count - 1);
            m_lHeap.RemoveAt(m_lHeap.Count - 1);
            BubbleDown(0);
            m_dLocation.Remove(data);
           // Debug.Assert(ValidateHeap());
            return data;
        }

        private bool ValidateHeap()
        {
            int idx = 0;
            for (idx = 0; idx < m_lHeap.Count; idx++)
            {
                if (LeftChild(idx) < m_lHeap.Count)
                    if (m_lHeap[idx].Priority > m_lHeap[LeftChild(idx)].Priority)
                        return false;
                if (RightChild(idx) < m_lHeap.Count)
                    if (m_lHeap[idx].Priority > m_lHeap[RightChild(idx)].Priority)
                        return false;
                if (m_dLocation[m_lHeap[idx].Data] != idx)
                    return false;

            }
            return true;
        }

        public bool IsEmpty()
        {
            return m_lHeap.Count == 0;
        }

        private void BubbleUp(int idx)
        {
            while (idx > 0 && m_lHeap[idx].Priority < m_lHeap[Parent(idx)].Priority)
            {
                Swap(idx, Parent(idx));
                idx = Parent(idx);
            }
        }

        private bool GreaterThanChildren(int idx)
        {
            int iLeftIdx = LeftChild(idx), iRightIdx = RightChild(idx);
            if (iLeftIdx < m_lHeap.Count && m_lHeap[idx].Priority > m_lHeap[iLeftIdx].Priority)
                return true;
            else if (iRightIdx < m_lHeap.Count && m_lHeap[idx].Priority > m_lHeap[iRightIdx].Priority)
                return true;
            return false;
        }
        private int GetLargerChild(int idx)
        {
            int iLeftIdx = LeftChild(idx), iRightIdx = RightChild(idx);
            if (iRightIdx >= m_lHeap.Count && iLeftIdx >= m_lHeap.Count)
                return - 1;
            if (iRightIdx < m_lHeap.Count)
            {
                if (m_lHeap[iLeftIdx].Priority > m_lHeap[iRightIdx].Priority)
                    return iRightIdx;
                return iLeftIdx;
            }
            return iLeftIdx;
        }

        private void BubbleDown(int idx)
        {
            while (idx != -1)
            {
                if (GreaterThanChildren(idx))
                {
                    int iChild = GetLargerChild(idx);
                    Swap(idx, iChild);
                    idx = iChild;
                }
                else
                    return;
            }
        }

        private int Parent(int idx)
        {
            return (idx - 1) / 2;
        }
        private int LeftChild(int idx)
        {
            return idx * 2 + 1;
        }
        private int RightChild(int idx)
        {
            return idx * 2 + 2;
        }

        public void Swap(int idx1, int idx2)
        {
            Pair<D> p1 = m_lHeap[idx1];
            Pair<D> p2 = m_lHeap[idx2];
            double priority = p1.Priority;
            p1.Priority = p2.Priority;
            p2.Priority = priority;
            D data = p1.Data;
            p1.Data = p2.Data;
            p2.Data = data;
            m_dLocation[p1.Data] = idx1;
            m_dLocation[p2.Data] = idx2;
        }


        private class Pair<D>
        {
            public D Data;
            public double Priority;
            public Pair(D data, double priority)
            {
                Data = data;
                Priority = priority;
            }
            public override string ToString()
            {
                return Data.ToString() + " - " + Priority;
            }
        }

        public double GetMaxPriority()
        {
            return m_lHeap[0].Priority;
        }
    }
}
