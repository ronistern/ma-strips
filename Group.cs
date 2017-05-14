using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class Group
    {
        public List<Predicate> group = new List<Predicate>();
        public int cost = 0;
        public Group()
        {

        }

        public Group(Group g)
        {
            group = g.group;
            cost = 0;
        }
    }
}
