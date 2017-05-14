using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    public class Rail
    {
        public int m_train;
        public int m_country1;
        public int m_city1;
        public int m_country2;
        public int m_city2;
        public Rail(int train,int country1, int city1, int country2, int city2)
        {
            m_train = train;

            m_country1 = country1;
            m_city1 = city1;

            m_country2 = country2;
            m_city2 = city2;
        }
    }
}
