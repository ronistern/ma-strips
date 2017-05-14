using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;

namespace Planning
{
    class ExternalPlanners
    {

        public static string ffPath = @"ff.exe";
        public static string fdPath = @"C:\cygwin\home\shlomi\FastDownward\src\";
        public static string cygwinPath = @"C:\cygwin\";
        public static string fdOutputPath = @"C:\cygwin\home\shlomi\";
        public ExternalPlanners()
        {
            // Console.WriteLine(" * ");
        }

        public List<string> Plan(bool bUseFF, bool bUseFD, Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions, int cMaxMilliseconds, out bool bUnsolvable)
        {
            //Program.KillPlanners();
            List<string> lPlan = null;


            if (privateActions != null)
                d.Actions = privateActions;
            if (goal != null)
                p.Goal = goal;

          //  string sFDPath = @"C:\cygwin\home\shlomi\FastDownward\src\";
            Process pFF = null, pFD = null;
            if (bUseFF)
                pFF = RunFF(d.WriteSimpleDomain(), p.WriteSimpleProblem(curentState));
            if (bUseFD)
                pFD = RunFD(d.WriteSimpleDomain(), p.WriteSimpleProblem(curentState));
            bUnsolvable = false;
            bool bFFDone = false, bFDDone = false;

            Process[] process;
            if (bUseFF && !bUseFD)
                process = new Process[] { pFF };
            else
                if (!bUseFF && bUseFD)
                process = new Process[] { pFD };
            else
                process = new Process[] { pFF, pFD };

            if (WaitForProcesses(process, cMaxMilliseconds, out bFFDone, out bFDDone))
            {
                if (bFFDone)
                {
                    //Console.WriteLine("Plan found by FF");
                    Thread.Sleep(150);
                    lPlan = ReadFFPlan(process[0].Id, out bUnsolvable);
                    KillAll(process.ToList());
                    Thread.Sleep(50);
                }
                else if (bFDDone)
                {
                    Console.WriteLine("Plan found by FD");
                    Thread.Sleep(100);
                    lPlan = ReadPlan(fdOutputPath);
                    KillAll(process.ToList());
                    Thread.Sleep(50);
                }
                return lPlan;
            }
            return null;
        }

        public List<string> Plan(string agent, bool bUseFF, bool bUseFD, Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions, int cMaxMilliseconds, out bool bUnsolvable)
        {
            //Program.KillPlanners();
            List<string> lPlan = null;


            if (privateActions != null)
                d.Actions = privateActions;
            if (goal != null)
                p.Goal = goal;

            string sFDPath = @"C:\cygwin\home\shlomi\FastDownward\src\";
            Process pFF = null, pFD = null;
            if (bUseFF)
                pFF = RunFF(d.WriteSimpleDomain(), p.WriteSimpleProblem(curentState));
            if (bUseFD)
                pFD = RunFD(agent, sFDPath, d.WriteSimpleDomain(), p.WriteSimpleProblem(curentState));
            bUnsolvable = false;
            bool bFFDone = false, bFDDone = false;
            Process[] process;
            if (bUseFF && !bUseFD)
                process = new Process[] { pFF };
            else
                if (!bUseFF && bUseFD)
                process = new Process[] { pFD };
            else
                process = new Process[] { pFF, pFD };

            if (WaitForProcesses(process, cMaxMilliseconds, out bFFDone, out bFDDone))
            {
                if (bFFDone)
                {
                    //  Console.WriteLine("Plan found by FF");
                    Thread.Sleep(200);
                    lPlan = ReadFFPlan(process[0].Id, out bUnsolvable);
                    KillAll(process.ToList());
                }
                else if (bFDDone)
                {
                    Console.WriteLine("Plan found by FD");
                    Thread.Sleep(100);
                    lPlan = ReadPlan(@"C:\cygwin\home\shlomi\");
                    KillAll(process.ToList());
                }
                return lPlan;
            }
            return null;
        }
        public List<string> ReadFFPlan(int iPID, out bool bUnsolvable)
        {
            string sOutput = FFOutput[iPID];
            MemoryStream planMs = new MemoryStream();
            if (sOutput.Contains("found legal plan as follows"))
            {
                string sPlan = sOutput.Substring(sOutput.IndexOf("found legal plan as follows"));
                sPlan = sPlan.Replace("found legal plan as follows", "").Trim();
                string[] asPlan = sPlan.Split('\n');
                string sFinalPlan = "";
                for (int i = 0; i < asPlan.Length; i++)
                {
                    if (!asPlan[i].Contains(":"))
                        break;
                    if (asPlan[i].Contains("time spent:"))
                        break;
                    sFinalPlan += asPlan[i].Substring(asPlan[i].IndexOf(':') + 2).Trim() + "\n";
                }
                StreamWriter sw = new StreamWriter(planMs);
                sw.WriteLine(sFinalPlan);
                sw.Close();
                bUnsolvable = false;
            }
            else
            {
                if (sOutput.Contains("goal can be simplified to TRUE"))
                {
                    bUnsolvable = false;
                    return new List<string>();

                }
                else if (sOutput.Contains("goal can be simplified to FALSE"))
                {

                    bUnsolvable = true;
                    return null;

                }
                else
                {
                    bUnsolvable = false;
                    return null;
                }
            }


            List<string> lPlan = ReadPlan(new MemoryStream(planMs.ToArray()));
            return lPlan;
        }

        public bool WaitForProcesses(Process[] a, int cMaxMilliseconds, out bool bFFDone, out bool bFDDone)
        {
            DateTime dtStart = DateTime.Now;
            bool bDone = false;
            bFFDone = false;
            bFDDone = false;

            while (!bDone)
            {
                bDone = false;
                a[0].WaitForExit(200);
                //List<Process> l = GetPlanningProcesses();
                foreach (Process p in a)
                {
                    if (p.HasExited)
                    {
                        if (p.StartInfo.FileName == ffPath)
                        {
                            bFFDone = true;
                            bFDDone = false;
                        }
                        else
                        {
                            bFFDone = false;
                            bFDDone = true;
                        }
                        bDone = true;
                    }
                }


                if (!bDone)
                {
                    try
                    {
                        TimeSpan ts = (DateTime.Now - dtStart);
                        if (ts.TotalMilliseconds > cMaxMilliseconds)
                        {
                            bDone = true;
                        }
                        bool bMemSizeLimitReached = false;
                        foreach (Process pPlanning in GetPlanningProcesses())
                        {
                            if (pPlanning.WorkingSet64 > 2 * Math.Pow(2, 30))
                            {
                                bMemSizeLimitReached = true;
                            }
                        }
                        if (bMemSizeLimitReached)
                        {
                            bDone = true;
                        }
                    }
                    catch (Exception e)
                    { }
                }

            }
            KillAll(a.ToList());
            List<Process> lPlanningProcesses = GetPlanningProcesses();
            KillAll(lPlanningProcesses);
            return bFDDone || bFFDone;
        }
        public static void KillPlanners()
        {

            List<Process> lPlanningProcesses = GetPlanningProcesses();
            KillAll(lPlanningProcesses);

        }
        public Process RunFD(MemoryStream msDomain, MemoryStream msProblem)
        {
            File.Delete(fdPath + "plan.txt");
            File.Delete(fdPath + "sas_plan");

            //for now, saving files in the working directory


            msProblem.Position = 0;
            msDomain.Position = 0;

            StreamWriter swDomainFile = new StreamWriter(fdPath + "dFD.pddl");
            StreamReader srDomain = new StreamReader(msDomain);
            swDomainFile.Write(srDomain.ReadToEnd());
            swDomainFile.Close();

            StreamWriter swProblemFile = new StreamWriter(fdPath + "pFD.pddl");
            StreamReader srProblem = new StreamReader(msProblem);
            swProblemFile.Write(srProblem.ReadToEnd());
            swProblemFile.Close();

            Process pFD = new Process();



          
            pFD.StartInfo.FileName = cygwinPath+@"bin\bash.exe";
            pFD.StartInfo.Arguments = "-l "+ fdPath+"plan ";
             pFD.StartInfo.Arguments += fdPath+"dFD.pddl "+ fdPath + "pFD.pddl";


            pFD.StartInfo.Arguments += " --heuristic \"hlm,hff=lm_ff_syn(lm_rhw(reasonable_orders=true,lm_cost_type=ONE,cost_type=ONE))\" " +
                                    " --search \"lazy_greedy([hff,hlm],preferred=[hff,hlm],cost_type=ONE)\"";

             pFD.StartInfo.UseShellExecute = false;
           

            pFD.StartInfo.RedirectStandardOutput = true;
            pFD.OutputDataReceived += new DataReceivedEventHandler(FDOutputHandler);


            FDProcesses = new HashSet<Process>();
            pFD.Start();
           
            pFD.BeginOutputReadLine();

            return pFD;
        }
        public Process RunFD(string sFDPath, MemoryStream msDomain, MemoryStream msProblem)
        {
            File.Delete(sFDPath + "plan.txt");
            File.Delete(sFDPath + "sas_plan");

            //for now, saving files in the working directory


            msProblem.Position = 0;
            msDomain.Position = 0;

            StreamWriter swDomainFile = new StreamWriter(sFDPath + "dFD.pddl");
            StreamReader srDomain = new StreamReader(msDomain);
            swDomainFile.Write(srDomain.ReadToEnd());
            swDomainFile.Close();

            StreamWriter swProblemFile = new StreamWriter(sFDPath + "pFD.pddl");
            StreamReader srProblem = new StreamReader(msProblem);
            swProblemFile.Write(srProblem.ReadToEnd());
            swProblemFile.Close();

            Process pFD = new Process();



            //  pFD.StartInfo.WorkingDirectory = @"C:\cygwin\bin\";

            pFD.StartInfo.FileName = @"C:\cygwin\bin\bash.exe";
            //pFD.StartInfo.Arguments = " -i /Cygwin-Terminal.ico -";// /Cygwin-Terminal.ico -";
            pFD.StartInfo.Arguments = "-l c:/cygwin/home/shlomi/FastDownward/src/plan ";
            //pFD.StartInfo.Arguments += "'--exec 'c:/cygwin/home/shlomi/FastDownward/src/plan' 'C:/cygwin/home/shlomi/FastDownward/src/dFD.pddl' 'C:/cygwin/home/shlomi/FastDownward/src/pFD.pddl'";
            pFD.StartInfo.Arguments += "C:/cygwin/home/shlomi/FastDownward/src/dFD.pddl C:/cygwin/home/shlomi/FastDownward/src/pFD.pddl";


            pFD.StartInfo.Arguments += " --heuristic \"hlm,hff=lm_ff_syn(lm_rhw(reasonable_orders=true,lm_cost_type=ONE,cost_type=ONE))\" " +
                                    " --search \"lazy_greedy([hff,hlm],preferred=[hff,hlm],cost_type=ONE)\"";


            //p.StartInfo.Arguments += " --heuristic \"hFF=ff(cost_type=1)\" " +
            //                       " --search \"lazy_greedy(hff, preferred=hff)\" ";
            pFD.StartInfo.UseShellExecute = false;
            // pFD.StartInfo.RedirectStandardInput = true;


            pFD.StartInfo.RedirectStandardOutput = true;
            pFD.OutputDataReceived += new DataReceivedEventHandler(FDOutputHandler);


            FDProcesses = new HashSet<Process>();
            pFD.Start();
            // Thread.Sleep(10000);
            // StreamWriter myStreamWriter = pFD.StandardInput;
            // myStreamWriter.WriteLine();
            //  myStreamWriter.WriteLine("cd cygwin");//home/shlomi/FastDownward/src/plan");
            // myStreamWriter.Close();
            pFD.BeginOutputReadLine();

            // string sr = pFD.StandardOutput.ReadLine();
            return pFD;
        }
        public Process RunFD(string name, string sFDPath, MemoryStream msDomain, MemoryStream msProblem)
        {
            try
            {
                name = name.Replace(" ", "");
                name = name.Replace(":", "");
                sFDPath = sFDPath + name + @"\";

                if (Directory.Exists(sFDPath))
                {
                    File.Delete(sFDPath + "plan.txt");
                    File.Delete(sFDPath + "sas_plan");
                }
                else
                {
                    Directory.CreateDirectory(sFDPath);
                }
                //for now, saving files in the working directory


                msProblem.Position = 0;
                msDomain.Position = 0;

                StreamWriter swDomainFile = new StreamWriter(sFDPath + "dFD.pddl");
                StreamReader srDomain = new StreamReader(msDomain);
                swDomainFile.Write(srDomain.ReadToEnd());
                swDomainFile.Close();

                StreamWriter swProblemFile = new StreamWriter(sFDPath + "pFD.pddl");
                StreamReader srProblem = new StreamReader(msProblem);
                swProblemFile.Write(srProblem.ReadToEnd());
                swProblemFile.Close();

                Process pFD = new Process();



                //  pFD.StartInfo.WorkingDirectory = @"C:\cygwin\bin\";
                // pFD.StartInfo.WorkingDirectory = @"C:\teeeemmp";
                pFD.StartInfo.FileName = @"C:\cygwin\bin\bash.exe";
                //pFD.StartInfo.Arguments = " -i /Cygwin-Terminal.ico -";// /Cygwin-Terminal.ico -";
                pFD.StartInfo.Arguments = "-l c:/cygwin/home/shlomi/FastDownward/src/plan ";
                //pFD.StartInfo.Arguments += "'--exec 'c:/cygwin/home/shlomi/FastDownward/src/plan' 'C:/cygwin/home/shlomi/FastDownward/src/dFD.pddl' 'C:/cygwin/home/shlomi/FastDownward/src/pFD.pddl'";
                pFD.StartInfo.Arguments += "C:/cygwin/home/shlomi/FastDownward/src/" + name + "/" + "dFD.pddl C:/cygwin/home/shlomi/FastDownward/src/" + name + "/" + "pFD.pddl";


                pFD.StartInfo.Arguments += " --heuristic \"hlm,hff=lm_ff_syn(lm_rhw(reasonable_orders=true,lm_cost_type=ONE,cost_type=ONE))\" " +
                                        " --search \"lazy_greedy([hff,hlm],preferred=[hff,hlm],cost_type=ONE)\"";


                //p.StartInfo.Arguments += " --heuristic \"hFF=ff(cost_type=1)\" " +
                //                       " --search \"lazy_greedy(hff, preferred=hff)\" ";
                pFD.StartInfo.UseShellExecute = false;
                // pFD.StartInfo.RedirectStandardInput = true;


                pFD.StartInfo.RedirectStandardOutput = true;
                pFD.OutputDataReceived += new DataReceivedEventHandler(FDOutputHandler);


                FDProcesses = new HashSet<Process>();
                pFD.Start();
                // Thread.Sleep(10000);
                // StreamWriter myStreamWriter = pFD.StandardInput;
                // myStreamWriter.WriteLine();
                //  myStreamWriter.WriteLine("cd cygwin");//home/shlomi/FastDownward/src/plan");
                // myStreamWriter.Close();
                pFD.BeginOutputReadLine();

                // string sr = pFD.StandardOutput.ReadLine();
                return pFD;
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.ToString());
            }
            return null;
        }
        static Mutex m = new Mutex();
        public Process RunFF(MemoryStream msDomain, MemoryStream msProblem)
        {
            msProblem.Position = 0;
            msDomain.Position = 0;


            m.WaitOne();
            Process pFF = new Process();

            pFF.StartInfo.FileName = ffPath;


            pFF.StartInfo.UseShellExecute = false;
            pFF.StartInfo.RedirectStandardInput = true;
            pFF.StartInfo.RedirectStandardOutput = true;
            pFF.OutputDataReceived += new DataReceivedEventHandler(FFOutputHandler);
            pFF.Start();
            FFOutput[pFF.Id] = "";
            pFF.BeginOutputReadLine();
            m.ReleaseMutex();

            StreamReader srOps = new StreamReader(msDomain);


            string domain = srOps.ReadToEnd();

            pFF.StandardInput.Write(domain);
            srOps.Close();
            BinaryWriter b = new BinaryWriter(pFF.StandardInput.BaseStream);
            b.Write('\0');

            StreamReader srFct = new StreamReader(msProblem);
            string problem = srFct.ReadToEnd();
            pFF.StandardInput.Write(problem);
            srFct.Close();

            b.Write('\0');
            //planer.StandardInput.Flush();

            pFF.StandardInput.Close();

            return pFF;
        }



        public List<string> FFPlan(Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions, int cMaxMilliseconds, out bool bUnsolvable)
        {
            //Program.KillPlanners();
            List<string> ffLplan = new List<string>();
            List<string> lPlan = new List<string>();


            if (privateActions != null)
                d.Actions = privateActions;
            if (goal != null)
                p.Goal = goal;

            MemoryStream msDomain = d.WriteSimpleDomain();
            MemoryStream problem_M_S = p.WriteSimpleProblem(curentState);


            /* StreamWriter swDomainFile = new StreamWriter(@"D:\tmp\testd.pddl",false);
             StreamReader srDomain = new StreamReader(msDomain);
             swDomainFile.Write(srDomain.ReadToEnd());
             swDomainFile.Close();

             StreamWriter swProblemFile = new StreamWriter(@"D:\tmp\testp.pddl", false);
             StreamReader srProblem = new StreamReader(problem_M_S);
             swProblemFile.Write(srProblem.ReadToEnd());
             swProblemFile.Close();
             */

            problem_M_S.Position = 0;
            msDomain.Position = 0;



            Process planer = new Process();
            //planer.StartInfo.WorkingDirectory = @"C:\project\Planning 2 new\PDDLTEST\temp";
            planer.StartInfo.FileName = "ff.exe";
            //planer.StartInfo.Arguments += "-o dT.pddl -f pT.pddl";

            if (!FFOutput.ContainsKey(planer.Id))
                FFOutput.Add(planer.Id,"");
            FFOutput[planer.Id] = "";

            planer.StartInfo.UseShellExecute = false;
            planer.StartInfo.RedirectStandardInput = true;
            planer.StartInfo.RedirectStandardOutput = true;
            planer.OutputDataReceived += new DataReceivedEventHandler(FFOutputHandler);
            planer.Start();
            planer.BeginOutputReadLine();
            StreamReader srOps = new StreamReader(msDomain);


            string domain = srOps.ReadToEnd();

            planer.StandardInput.Write(domain);
            srOps.Close();
            BinaryWriter b = new BinaryWriter(planer.StandardInput.BaseStream);
            b.Write('\0');

            StreamReader srFct = new StreamReader(problem_M_S);
            string problem = srFct.ReadToEnd();
            planer.StandardInput.Write(problem);
            srFct.Close();

            b.Write('\0');
            //planer.StandardInput.Flush();

            planer.StandardInput.Close();

            if (cMaxMilliseconds != -1)
            {
                if (!planer.WaitForExit(cMaxMilliseconds))//2 minutes max
                {
                    planer.Kill();
                    bUnsolvable = false;
                    return null;
                }
            }

            planer.WaitForExit();
            planer.Close();
            //string sOutput = planer.StandardOutput.ReadToEnd();
            //Thread.Sleep(1000);
            string sOutput = FFOutput[planer.Id];
            //throw new NotImplementedException();
            //Console.WriteLine(sOutput);
            MemoryStream planMs = new MemoryStream();
            if (sOutput.Contains("found legal plan as follows"))
            {
                string sPlan = sOutput.Substring(sOutput.IndexOf("found legal plan as follows"));
                sPlan = sPlan.Replace("found legal plan as follows", "").Trim();
                string[] asPlan = sPlan.Split('\n');
                string sFinalPlan = "";
                for (int i = 0; i < asPlan.Length; i++)
                {
                    if (!asPlan[i].Contains(":"))
                        break;
                    if (asPlan[i].Contains("time spent:"))
                        break;
                    sFinalPlan += asPlan[i].Substring(asPlan[i].IndexOf(':') + 2).Trim() + "\n";
                }
                StreamWriter sw = new StreamWriter(planMs);
                sw.WriteLine(sFinalPlan);
                sw.Close();
                bUnsolvable = false;
            }
            else
            {
                if (sOutput.Contains("goal can be simplified to TRUE"))
                {
                    ffLplan = new List<string>();
                    bUnsolvable = false;
                    return ffLplan;

                }
                else if (sOutput.Contains("goal can be simplified to FALSE"))
                {

                    ffLplan = null;
                    bUnsolvable = true;
                    return null;

                }
                else
                {
                    ffLplan = null;
                    bUnsolvable = false;
                    return null;
                }
            }


            lPlan = ReadPlan(new MemoryStream(planMs.ToArray()));
            ffLplan = lPlan;
            return lPlan;

        }
        public List<string> PdbFFPlan(Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions, int cMaxMilliseconds, out bool bUnsolvable)
        {
            Program.KillPlanners();
            List<string> ffLplan = new List<string>();
            List<string> lPlan = new List<string>();


            if (privateActions != null)
                d.Actions = privateActions;
            if (goal != null)
                p.Goal = goal;

            MemoryStream msDomain = d.WriteSimpleDomain();
            MemoryStream problem_M_S = p.WriteSimpleProblem(curentState);


            //StreamWriter swDomainFile = new StreamWriter(@"C:\Dropbox-users\shlomi\Dropbox\Dropbox\privacyPreserving\Competition\all\factored\testd.pddl");
            // StreamReader srDomain = new StreamReader(msDomain);
            // swDomainFile.Write(srDomain.ReadToEnd());
            // swDomainFile.Close();

            // StreamWriter swProblemFile = new StreamWriter(@"C:\Dropbox-users\shlomi\Dropbox\Dropbox\privacyPreserving\Competition\all\factored\testp.pddl");
            //  StreamReader srProblem = new StreamReader(problem_M_S);
            // swProblemFile.Write(srProblem.ReadToEnd());
            // swProblemFile.Close();


            problem_M_S.Position = 0;
            msDomain.Position = 0;



            Process planer = new Process();
            //planer.StartInfo.WorkingDirectory = @"C:\project\Planning 2 new\PDDLTEST\temp";
            planer.StartInfo.FileName = "ff.exe";
            //planer.StartInfo.Arguments += "-o dT.pddl -f pT.pddl";

            FFOutput[planer.Id] = "";

            planer.StartInfo.UseShellExecute = false;
            planer.StartInfo.RedirectStandardInput = true;
            planer.StartInfo.RedirectStandardOutput = true;
            planer.OutputDataReceived += new DataReceivedEventHandler(FFOutputHandler);
            planer.Start();
            planer.BeginOutputReadLine();
            StreamReader srOps = new StreamReader(msDomain);


            string domain = srOps.ReadToEnd();

            planer.StandardInput.Write(domain);
            srOps.Close();
            BinaryWriter b = new BinaryWriter(planer.StandardInput.BaseStream);
            b.Write('\0');

            StreamReader srFct = new StreamReader(problem_M_S);
            string problem = srFct.ReadToEnd();
            planer.StandardInput.Write(problem);
            srFct.Close();

            b.Write('\0');
            //planer.StandardInput.Flush();

            planer.StandardInput.Close();

            if (cMaxMilliseconds != -1)
            {
                if (!planer.WaitForExit(cMaxMilliseconds))//2 minutes max
                {
                    planer.Kill();
                    bUnsolvable = false;
                    return null;
                }
            }
            else
                planer.WaitForExit();
            planer.Close();
            //string sOutput = planer.StandardOutput.ReadToEnd();
            // planer.WaitForExit();
            string sOutput = FFOutput[planer.Id];
            //throw new NotImplementedException();
            //Console.WriteLine(sOutput);
            MemoryStream planMs = new MemoryStream();
            if (sOutput.Contains("found legal plan as follows"))
            {
                string sPlan = sOutput.Substring(sOutput.IndexOf("found legal plan as follows"));
                sPlan = sPlan.Replace("found legal plan as follows", "").Trim();
                string[] asPlan = sPlan.Split('\n');
                string sFinalPlan = "";
                for (int i = 0; i < asPlan.Length; i++)
                {
                    if (!asPlan[i].Contains(":"))
                        break;
                    if (asPlan[i].Contains("time spent:"))
                        break;
                    sFinalPlan += asPlan[i].Substring(asPlan[i].IndexOf(':') + 2).Trim() + "\n";
                }
                StreamWriter sw = new StreamWriter(planMs);
                sw.WriteLine(sFinalPlan);
                sw.Close();
                bUnsolvable = false;
            }
            else
            {
                if (sOutput.Contains("goal can be simplified to TRUE"))
                {
                    ffLplan = new List<string>();
                    bUnsolvable = false;
                    return ffLplan;

                }
                else if (sOutput.Contains("goal can be simplified to FALSE"))
                {

                    ffLplan = null;
                    bUnsolvable = true;
                    return null;

                }
                else
                {
                    ffLplan = null;
                    bUnsolvable = false;
                    return null;
                }
            }


            lPlan = ReadPlan(new MemoryStream(planMs.ToArray()));
            ffLplan = lPlan;
            return lPlan;

        }

        Dictionary<int, string> FFOutput = new Dictionary<int, string>();
        private void FFOutputHandler(object sendingProcess,
          DataReceivedEventArgs outLine)
        {
            Process p = (Process)sendingProcess;
            if (!String.IsNullOrEmpty(outLine.Data))
            {
                FFOutput[p.Id] += outLine.Data + Environment.NewLine;
            }
        }

        private HashSet<Process> FDProcesses = null;

        string FDOutput = "";
        private void FDOutputHandler(object sendingProcess,
           DataReceivedEventArgs outLine)
        {
            FDProcesses.Add((Process)sendingProcess);
            Process p = (Process)sendingProcess;
            if (!String.IsNullOrEmpty(outLine.Data))
            {
                FDOutput += outLine.Data + Environment.NewLine;
            }
        }



        public static List<Process> GetPlanningProcesses()
        {
            List<Process> l = new List<Process>();
            foreach (Process p in Process.GetProcesses())
            {
                if ((p.ProcessName.ToLower().Contains("downward") || p.ProcessName.ToLower().Contains("ff")) && (!p.ProcessName.ToLower().Contains("office")))
                    l.Add(p);
            }
            return l;
        }


        public bool RunProcessII(Process p, int cMaxMilliseconds)
        {
            p.StartInfo.UseShellExecute = false;
            p.StartInfo.RedirectStandardOutput = true;
            p.OutputDataReceived += new DataReceivedEventHandler(FDOutputHandler);

            DateTime dtStart = DateTime.Now;
            p.Start();
            p.BeginOutputReadLine();

            if (!p.WaitForExit(cMaxMilliseconds))
                p.Kill();
            p.Close();
            return true;
        }

        public bool RunProcess(Process p, int cMaxMilliseconds)
        {
            p.StartInfo.UseShellExecute = false;
            p.StartInfo.RedirectStandardOutput = true;
            p.OutputDataReceived += new DataReceivedEventHandler(FDOutputHandler);

            DateTime dtStart = DateTime.Now;
            bool bDone = false;
            FDProcesses = new HashSet<Process>();
            p.Start();
            p.BeginOutputReadLine();

            while (!bDone)
            {
                if (!p.HasExited)
                    bDone = p.WaitForExit(10000);
                else
                    bDone = true;
                if (!bDone)
                {
                    try
                    {
                        TimeSpan ts = (DateTime.Now - dtStart);
                        List<Process> l = GetPlanningProcesses();
                        if (ts.TotalMilliseconds > cMaxMilliseconds)
                        {
                            l.Add(p);
                            KillAll(l);
                            return false;
                        }
                        bool bMemSizeLimitReached = false;
                        foreach (Process pPlanning in GetPlanningProcesses())
                        {
                            if (pPlanning.WorkingSet64 > 2 * Math.Pow(2, 30))
                            {
                                bMemSizeLimitReached = true;
                            }
                        }
                        if (bMemSizeLimitReached)
                        {
                            l.Add(p);
                            KillAll(l);
                            return false;
                        }
                    }
                    catch (Exception e)
                    {
                        Console.WriteLine("fd-fails");
                    }
                }

            }
            p.Close();
            return true;
        }

        public static void KillAll(List<Process> l)
        {

            foreach (Process p in l)
            {
                try
                {
                    if (!p.HasExited)
                    {
                        
                        p.Kill();
                       // p.WaitForExit();
                         Thread.Sleep(300);
                         //p.WaitForExit();
                        p.Close();


                    }
                }
                catch (Exception e)
                {
                    //Console.WriteLine("*");
                }


            }


        }

        public bool RunFD(string sPath, int cMaxMilliseconds)
        {
            Process p = new Process();
            p.StartInfo.WorkingDirectory = sPath;
            //p.StartInfo.FileName = Program.BASE_PATH + @"\PDDL\Planners\ff.exe";
            p.StartInfo.FileName = @"C:\cygwin\bin\bash.exe";
            p.StartInfo.Arguments = @"C:\cygwin\home\shlomi\FastDownward\src\plan";
            // p.StartInfo.Arguments = @"C:\cygwin\home\shlomi\FastDownward\src\plan";
            p.StartInfo.Arguments += @" dFD.pddl pFD.pddl";


            p.StartInfo.Arguments += " --heuristic \"hlm,hff=lm_ff_syn(lm_rhw(reasonable_orders=true,lm_cost_type=ONE,cost_type=ONE))\" " +
                                    " --search \"lazy_greedy([hff,hlm],preferred=[hff,hlm],cost_type=ONE)\"";
            //p.StartInfo.Arguments += " --heuristic \"hFF=ff(cost_type=1)\" " +
            //                       " --search \"lazy_greedy(hff, preferred=hff)\" ";
            if (!RunProcess(p, cMaxMilliseconds))
                return false;

            return true;
        }


        public List<string> FDPlan(Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions, int cMaxMilliseconds, out bool bUnsolvable)
        {
            Program.KillPlanners();
            List<string> ffLplan = new List<string>();
            List<string> lPlan = new List<string>();

            File.Delete("plan.txt");
            File.Delete("sas_plan");

            if (privateActions != null)
                d.Actions = privateActions;
            if (goal != null)
                p.Goal = goal;

            MemoryStream msDomain = d.WriteSimpleDomain();
            MemoryStream problem_M_S = p.WriteSimpleProblem(curentState);

            //for now, saving files in the working directory

            StreamWriter swDomainFile = new StreamWriter("dFD.pddl");
            StreamReader srDomain = new StreamReader(msDomain);
            swDomainFile.Write(srDomain.ReadToEnd());
            swDomainFile.Close();

            StreamWriter swProblemFile = new StreamWriter("pFD.pddl");
            StreamReader srProblem = new StreamReader(problem_M_S);
            swProblemFile.Write(srProblem.ReadToEnd());
            swProblemFile.Close();


            problem_M_S.Position = 0;
            msDomain.Position = 0;

            bUnsolvable = false;

            if (RunFD("./", cMaxMilliseconds))
                return ReadPlan("./");
            return null;
        }

        private List<string> ReadPlan(string sPath)
        {
            List<string> lPlan = new List<string>();
            string sPlanFile = "plan.txt";
            if (File.Exists(sPath + sPlanFile))
            {
                StreamReader sr = new StreamReader(sPath + sPlanFile);
                while (!sr.EndOfStream)
                {
                    string sAction = sr.ReadLine().Trim().ToLower();
                    if (sAction != "")
                        lPlan.Add(sAction);
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "mipsSolution.soln"))
            {
                StreamReader sr = new StreamReader(sPath + "mipsSolution.soln");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        int iEnd = sLine.IndexOf(")");
                        sLine = sLine.Substring(iStart + 1, iEnd - iStart - 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "sas_plan"))
            {
                StreamReader sr = new StreamReader(sPath + "sas_plan");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    sLine = sLine.Replace("(", "");
                    sLine = sLine.Replace(")", "");
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        sLine = sLine.Substring(iStart + 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else
            {


                return null;
            }

            List<string> lFilteredPlan = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.Contains("-remove") ||
                    sAction.Contains("-translate"))
                    continue;
                if (sAction.Contains("-add"))
                    lFilteredPlan.Add(sAction.Replace("-add", ""));
                else
                    lFilteredPlan.Add(sAction);

            }

            return lFilteredPlan;
        }


        public List<string> ReadPlan(MemoryStream ms)
        {
            List<string> lPlan = new List<string>();

            StreamReader sr = new StreamReader(ms);

            while (!sr.EndOfStream)
            {
                string sAction = sr.ReadLine().Trim().ToLower();
                if (sAction != "")
                    lPlan.Add(sAction);
            }
            sr.Close();
            return lPlan;



            List<string> lFilteredPlan = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.Contains("-remove") ||
                    sAction.Contains("-translate"))
                    continue;
                if (sAction.Contains("-add"))
                    lFilteredPlan.Add(sAction.Replace("-add", ""));
                else
                    lFilteredPlan.Add(sAction);

            }

            return lFilteredPlan;
        }

        public List<string> ManualSolve(Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions, int cMaxMilliseconds, out bool bUnsolvable)
        {
            Program.KillPlanners();
            List<string> ffLplan = new List<string>();
            List<string> lPlan = new List<string>();


            if (privateActions != null)
                d.Actions = privateActions;
            if (goal != null)
                p.Goal = goal;
            bUnsolvable = false;
            return ManualSolve(p, d);
        }


        public List<string> ManualSolve(Problem p, Domain d)
        {
            List<string> lPlan = new List<string>();
            State sStart = new State(p);
            foreach (GroundedPredicate gp in p.Known)
                sStart.AddPredicate(gp);
            State sCurrent = null, sNext = null;
            Dictionary<State, Action> dMapStateToGeneratingAction = new Dictionary<State, Action>();
            dMapStateToGeneratingAction[sStart] = null;
            Dictionary<State, State> dParents = new Dictionary<State, State>();
            dParents[sStart] = null;
            int cProcessed = 0;
            List<string> lActionNames = new List<string>();

            sCurrent = sStart;
            while (!p.IsGoalState(sCurrent))
            {
                List<Action> lActions = new List<Action>(d.GroundAllActions(sCurrent.Predicates, false));
                Console.WriteLine("Available actions:");
                for (int i = 0; i < lActions.Count; i++)
                {
                    Console.WriteLine(i + ") " + lActions[i].Name);
                }
                Console.Write("Choose action number: ");
                int iAction = int.Parse(Console.ReadLine());
                Action a = lActions[iAction];
                sNext = sCurrent.Apply(a);

                lPlan.Add(a.Name);

                foreach (Predicate pNew in sNext.Predicates)
                    if (!sCurrent.Predicates.Contains(pNew))
                        Console.WriteLine(pNew);

                if (!dParents.Keys.Contains(sNext))
                {
                    dParents[sNext] = sCurrent;
                    dMapStateToGeneratingAction[sNext] = a;
                }

                sCurrent = sNext;

                cProcessed++;
            }
            return lPlan;
            //return GeneratePlan(sCurrent, null, dParents, dMapStateToGeneratingAction);
        }


    }
}
