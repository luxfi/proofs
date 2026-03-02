import { ExternalLink, ShieldCheck } from 'lucide-react'
import type { ProofConfig, ProofTool, ProofStatus } from '@/config/proofs'

interface ProofCardProps {
  proof: ProofConfig
}

const toolLabels: Record<ProofTool, string> = {
  lean4: 'Lean 4',
  halmos: 'Halmos',
  foundry: 'Foundry',
}

const statusLabels: Record<ProofStatus, string> = {
  proved: 'Proved',
  partial: 'Partial',
  axiom: 'Axiom',
}

const statusStyles: Record<ProofStatus, string> = {
  proved: 'bg-green-500/10 text-green-600 dark:text-green-400',
  partial: 'bg-yellow-500/10 text-yellow-600 dark:text-yellow-400',
  axiom: 'bg-blue-500/10 text-blue-600 dark:text-blue-400',
}

export function ProofCard({ proof }: ProofCardProps) {
  return (
    <article className="group rounded-lg border border-border/60 bg-card hover:border-border transition-colors">
      <div className="p-5">
        <div className="flex items-center justify-between mb-3">
          <div className="flex items-center gap-2">
            <span className="px-2 py-0.5 text-[11px] font-mono bg-accent text-accent-foreground rounded">
              {toolLabels[proof.tool]}
            </span>
            <span className={`px-2 py-0.5 text-[11px] font-mono rounded ${statusStyles[proof.status]}`}>
              {statusLabels[proof.status]}
            </span>
          </div>
          <ShieldCheck className="h-4 w-4 text-muted-foreground/50" />
        </div>

        <h2 className="text-base font-semibold mb-1 text-foreground group-hover:text-foreground/90">
          {proof.title}
        </h2>

        <h3 className="text-sm text-muted-foreground mb-3">
          {proof.subtitle}
        </h3>

        <p className="text-sm text-muted-foreground/80 mb-4 line-clamp-3 leading-relaxed">
          {proof.abstract}
        </p>

        <div className="flex items-center gap-3 mb-4 text-xs text-muted-foreground">
          <span className="font-mono">
            {proof.theoremCount} {proof.theoremCount === 1 ? 'theorem' : 'theorems'}
          </span>
          <span>·</span>
          <span>{proof.authors.join(' · ')}</span>
        </div>

        <div className="flex flex-wrap gap-1.5 mb-4">
          {proof.tags.slice(0, 4).map((tag) => (
            <span
              key={tag}
              className="px-2 py-0.5 text-[11px] font-mono bg-accent text-accent-foreground rounded"
            >
              {tag}
            </span>
          ))}
        </div>

        <div className="flex gap-2 pt-3 border-t border-border/40">
          <a
            href={proof.sourceUrl}
            target="_blank"
            rel="noopener noreferrer"
            className="flex-1 flex items-center justify-center gap-1.5 px-3 py-1.5 text-sm font-medium bg-foreground text-background rounded-md hover:bg-foreground/90 transition-colors"
          >
            <ShieldCheck className="h-3.5 w-3.5" />
            Source
          </a>
          <a
            href={proof.githubUrl}
            target="_blank"
            rel="noopener noreferrer"
            className="px-3 py-1.5 text-sm font-medium border border-border rounded-md text-muted-foreground hover:text-foreground hover:border-foreground/30 transition-colors"
          >
            Repo
          </a>
        </div>

        {proof.relatedPapers && proof.relatedPapers.length > 0 && (
          <div className="mt-3 pt-3 border-t border-border/30">
            {proof.relatedPapers.map((paper, i) => (
              <a
                key={i}
                href={`https://papers.lux.network`}
                target="_blank"
                rel="noopener noreferrer"
                className="flex items-center gap-1 text-xs text-muted-foreground hover:text-foreground transition-colors"
              >
                <ExternalLink className="h-3 w-3" />
                {paper}
              </a>
            ))}
          </div>
        )}
      </div>
    </article>
  )
}
