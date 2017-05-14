using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    public class ComparerArray : IEqualityComparer<int[]>
    {
        public bool Equals(int[] x, int[] y)
        {
            if (x.Length != y.Length)
                return false;
            for (int i = 0; i < x.Length; i++)
                if (x[i] != y[i])
                    return false;
            return true;
        }

        private int m_iHashCode = 0;

        public int GetHashCode(int[] obj)
        {
            if (m_iHashCode == 0)
            {
                for (int i = 0; i < obj.Length; i++)
                {

                    m_iHashCode = m_iHashCode * 100 + obj[i];
                    
                }
            }
            return m_iHashCode;
        }
    }
}
