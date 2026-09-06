import { ResultsContent } from '@/components/results-content';
import paper from '@/content/paper.json';
export default function Home() {
  return (
    <div className="page">
      <div className="page-title">
        <div className="eyebrow">A mathematical companion</div>
        <h1>{paper.manuscript.title}</h1>
        <p>Antonio Acuaviva</p>
      </div>
      <p className="results-introduction">
        This website accompanies the paper and presents the formal verification
        of its principal results in Lean. Each mathematical statement appears
        alongside its Lean formulation, with expandable, step-by-step
        explanations.
      </p>
      <ResultsContent />
    </div>
  );
}
