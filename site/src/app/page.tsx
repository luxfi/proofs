import { siteConfig } from '@/config/proofs'
import { Header } from '@/components/Header'
import { ProofCard } from '@/components/ProofCard'
import { Footer } from '@/components/Footer'

export default function Home() {
  const proofCount = siteConfig.proofs.length
  const totalTheorems = siteConfig.proofs.reduce((sum, p) => sum + p.theoremCount, 0)

  return (
    <div className="min-h-svh flex flex-col">
      <Header config={siteConfig} />

      <main className="flex-1">
        <div className="max-w-7xl mx-auto px-6 pt-16 pb-12">
          <p className="text-sm font-mono text-muted-foreground mb-3">
            {proofCount} proofs · {totalTheorems} theorems
          </p>
          <h1 className="text-4xl md:text-5xl font-bold tracking-tight mb-4">
            {siteConfig.name}
            <span className="block text-muted-foreground text-2xl md:text-3xl font-normal mt-1">
              Formal Proofs
            </span>
          </h1>
          <p className="text-lg text-muted-foreground max-w-2xl leading-relaxed">
            {siteConfig.description}
          </p>
        </div>

        <div className="max-w-7xl mx-auto px-6 pb-20">
          {proofCount > 0 ? (
            <div className="grid gap-4 sm:grid-cols-2 lg:grid-cols-3">
              {siteConfig.proofs.map((proof) => (
                <ProofCard key={proof.id} proof={proof} />
              ))}
            </div>
          ) : (
            <div className="text-center py-20">
              <p className="text-muted-foreground">Proofs coming soon...</p>
            </div>
          )}
        </div>
      </main>

      <Footer config={siteConfig} />
    </div>
  )
}
