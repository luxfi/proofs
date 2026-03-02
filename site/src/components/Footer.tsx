import type { SiteConfig } from '@/config/proofs'

interface FooterProps {
  config: SiteConfig
}

export function Footer({ config }: FooterProps) {
  return (
    <footer className="border-t border-border/50 mt-20">
      <div className="max-w-7xl mx-auto px-6 py-8">
        <div className="flex flex-col md:flex-row items-center justify-between gap-4">
          <p className="text-sm text-muted-foreground">
            &copy; {new Date().getFullYear()} {config.fullName}
          </p>
          <div className="flex items-center gap-5 text-sm">
            <a
              href={config.website}
              target="_blank"
              rel="noopener noreferrer"
              className="text-muted-foreground hover:text-foreground transition-colors"
            >
              Website
            </a>
            <a
              href={config.github}
              target="_blank"
              rel="noopener noreferrer"
              className="text-muted-foreground hover:text-foreground transition-colors"
            >
              GitHub
            </a>
          </div>
        </div>
      </div>
    </footer>
  )
}
